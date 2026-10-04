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
# The Lovász–Plummer conjecture (proved 2011) and Sheehan's conjecture

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Petersen%27s_theorem#Related_conjectures)
* [LP86] Lovász, L. and Plummer, M. D. (1986). *Matching Theory.* North-Holland.
* [EKKKN11] Esperet, L., Kardoš, F., King, A. D., Král', D. and Norine, S. (2011).
  "Exponentially many perfect matchings in cubic graphs." *Adv. Math.* 227, pp. 1646--1664.
  [arXiv:1012.2878](https://arxiv.org/abs/1012.2878)
* [Sh77] Sheehan, J. (1977). "The multiplicity of Hamiltonian circuits in a graph." In *Recent
  Advances in Graph Theory*, Academia, Prague, pp. 477--480.
* [Th98] Thomassen, C. (1998). "Independent dominating sets and a second Hamiltonian cycle in
  regular graphs." *J. Combin. Theory Ser. B* 72, pp. 104--109.
-/

@[expose] public section

open SimpleGraph

namespace LovaszPlummerConjecture

variable {V : Type*}

/-- The number of perfect matchings of `G`. -/
noncomputable def perfectMatchingCount (G : SimpleGraph V) : ℕ :=
  {M : G.Subgraph | M.IsPerfectMatching}.ncard

/-- The edge `e` (with ends `α e`, `β e`) has exactly one end in `T`. -/
def epCross {W E : Type*} (α β : E → W) (T : Finset W) (e : E) : Prop :=
  (α e ∈ T ∧ β e ∉ T) ∨ (α e ∉ T ∧ β e ∈ T)

open Classical in
/-- The cut `δ(T)`. -/
noncomputable def epCut {W E : Type*} [Fintype E] (α β : E → W) (T : Finset W) : Finset E :=
  Finset.univ.filter (epCross α β T)

/-- The polytope given by nonnegativity, the degree constraints on the vertices in `L`
and the odd cut constraints. Loops carry weight `0`. -/
def epQ {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) : Set (E → ℝ) :=
  {x | (∀ e, 0 ≤ x e) ∧ (∀ e, α e = β e → x e = 0) ∧
    (∀ c ∈ L, ∑ e ∈ epCut α β {c}, x e = 1) ∧
    ∀ T ⊆ L, Odd T.card → 1 ≤ ∑ e ∈ epCut α β T, x e}

/-- Perfect matchings of the multigraph on `L` with edges `E`: loop-free edge sets meeting
every vertex of `L` exactly once. -/
def epPM {W E : Type*} (α β : E → W) (L : Finset W) : Set (Finset E) :=
  {M | (∀ e ∈ M, α e ≠ β e) ∧ ∀ c ∈ L, ∃! e, e ∈ M ∧ epCross α β {c} e}

open Classical in
/-- Indicator vector of an edge set. -/
noncomputable def epInd {E : Type*} (M : Finset E) : E → ℝ := fun e => if e ∈ M then 1 else 0

lemma mem_epCut {W E : Type*} [Fintype E] (α β : E → W) (T : Finset W) (e : E) :
    e ∈ epCut α β T ↔ epCross α β T e := by
  classical
  simp [epCut]

lemma epCross_singleton {W E : Type*} (α β : E → W) (c : W) (e : E) :
    epCross α β {c} e ↔ (α e = c ∧ β e ≠ c) ∨ (α e ≠ c ∧ β e = c) := by
  simp [epCross]

lemma epQ_le_one {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (hL : ∀ e, α e ∈ L ∧ β e ∈ L) {x : E → ℝ} (hx : x ∈ epQ α β L) (e : E) : x e ≤ 1 := by
  classical
  obtain ⟨h0, hloop, hdeg, -⟩ := hx
  by_cases h : α e = β e
  · rw [hloop e h]; exact zero_le_one
  · rw [← hdeg (α e) (hL e).1]
    refine Finset.single_le_sum (f := x) (fun i _ => h0 i) ?_
    rw [mem_epCut, epCross_singleton]
    exact Or.inl ⟨rfl, fun h' => h h'.symm⟩

lemma epQ_convex {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) :
    Convex ℝ (epQ α β L) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨x0, xl, xd, xo⟩ := hx
  obtain ⟨y0, yl, yd, yo⟩ := hy
  have hsum : ∀ s : Finset E, ∑ e ∈ s, (a • x + b • y) e =
      a * ∑ e ∈ s, x e + b * ∑ e ∈ s, y e := by
    intro s
    simp [Finset.sum_add_distrib, Finset.mul_sum]
  refine ⟨fun e => ?_, fun e he => ?_, fun c hc => ?_, fun T hT hodd => ?_⟩
  · have := x0 e; have := y0 e
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; positivity
  · simp [xl e he, yl e he]
  · rw [hsum, xd c hc, yd c hc]; linarith
  · rw [hsum]
    have := xo T hT hodd; have := yo T hT hodd
    nlinarith

lemma epQ_closed {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) :
    IsClosed (epQ α β L) := by
  have hcont : ∀ s : Finset E, Continuous fun x : E → ℝ => ∑ e ∈ s, x e := fun s =>
    continuous_finsetSum _ (fun e _ => continuous_apply e)
  have : epQ α β L = (⋂ e, {x : E → ℝ | 0 ≤ x e}) ∩ ((⋂ e, ⋂ (_ : α e = β e), {x : E → ℝ | x e = 0}) ∩
      ((⋂ c, ⋂ (_ : c ∈ L), {x : E → ℝ | ∑ e ∈ epCut α β {c}, x e = 1}) ∩
        (⋂ T, ⋂ (_ : T ⊆ L), ⋂ (_ : Odd T.card), {x : E → ℝ | 1 ≤ ∑ e ∈ epCut α β T, x e}))) := by
    ext x
    simp only [epQ, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [this]
  refine IsClosed.inter (isClosed_iInter fun e => isClosed_le continuous_const (continuous_apply e))
    (IsClosed.inter (isClosed_iInter fun e => isClosed_iInter fun _ =>
      isClosed_eq (continuous_apply e) continuous_const)
    (IsClosed.inter (isClosed_iInter fun c => isClosed_iInter fun _ =>
      isClosed_eq (hcont _) continuous_const)
    (isClosed_iInter fun T => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_le continuous_const (hcont _))))

lemma epQ_compact {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (hL : ∀ e, α e ∈ L ∧ β e ∈ L) : IsCompact (epQ α β L) := by
  refine IsCompact.of_isClosed_subset (isCompact_univ_pi fun _ : E => isCompact_Icc (a := (0 : ℝ))
    (b := 1)) (epQ_closed α β L) ?_
  intro x hx e _
  exact ⟨hx.1 e, epQ_le_one α β L hL hx e⟩

/-- A convex combination of indicator vectors lies in the convex hull. -/
lemma ep_hull_of_family {E : Type*} [Fintype E] {ι : Type*} [Fintype ι] (S : Set (Finset E))
    (w : ι → ℝ) (N : ι → Finset E) (hw : ∀ i, 0 ≤ w i) (hN : ∀ i, w i ≠ 0 → N i ∈ S)
    (h1 : ∑ i, w i = 1) (x : E → ℝ) (hx : ∀ e, x e = ∑ i, w i * epInd (N i) e) :
    x ∈ convexHull ℝ (epInd '' S) := by
  classical
  have hx' : x = ∑ i ∈ Finset.univ.filter (fun i => w i ≠ 0), w i • epInd (N i) := by
    funext e
    rw [hx e, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_filter_of_ne]
    intro i _ hi h0
    exact hi (by rw [h0, zero_mul])
  rw [hx']
  refine Convex.sum_mem (convex_convexHull ℝ _) (fun i _ => hw i) ?_ (fun i hi => ?_)
  · rw [Finset.sum_filter_of_ne (fun i _ hi => hi)]; exact h1
  · exact subset_convexHull ℝ _ ⟨N i, hN i (Finset.mem_filter.mp hi).2, rfl⟩

/-- Canonical form of a point of the convex hull of indicator vectors. -/
lemma ep_hull_repr {E : Type*} [Fintype E] (S : Set (Finset E)) (x : E → ℝ)
    (hx : x ∈ convexHull ℝ (epInd '' S)) :
    ∃ w : Finset E → ℝ, (∀ M, 0 ≤ w M) ∧ (∀ M, w M ≠ 0 → M ∈ S) ∧ ∑ M, w M = 1 ∧
      ∀ e, x e = ∑ M, w M * epInd M e := by
  classical
  refine convexHull_min (t := {x : E → ℝ | ∃ w : Finset E → ℝ, (∀ M, 0 ≤ w M) ∧
      (∀ M, w M ≠ 0 → M ∈ S) ∧ ∑ M, w M = 1 ∧ ∀ e, x e = ∑ M, w M * epInd M e}) ?_ ?_ hx
  · rintro _ ⟨M, hM, rfl⟩
    refine ⟨Pi.single M 1, fun M' => ?_, fun M' h => ?_, by simp, fun e => ?_⟩
    rotate_left 2
    · rw [Finset.sum_eq_single M]
      · rw [Pi.single_eq_same, one_mul]
      · intro b _ hb; rw [Pi.single_eq_of_ne hb, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [Pi.single_apply]; split_ifs <;> norm_num
    · by_cases h' : M' = M
      · subst h'; exact hM
      · exact absurd (Pi.single_eq_of_ne h' _) h
  · rintro x ⟨w, hw, hS, h1, hx⟩ y ⟨w', hw', hS', h1', hy⟩ a b ha hb hab
    refine ⟨fun M => a * w M + b * w' M, fun M => ?_, fun M h => ?_, ?_, fun e => ?_⟩
    · have := hw M; have := hw' M; positivity
    · by_contra hM
      have h1 : w M = 0 := by by_contra h0; exact hM (hS M h0)
      have h2 : w' M = 0 := by by_contra h0; exact hM (hS' M h0)
      exact h (show a * w M + b * w' M = 0 by rw [h1, h2]; ring)
    · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h1, h1']; linarith
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hx e, hy e, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun M _ => by ring

/-- Reduction to extreme points (Krein–Milman). -/
lemma ep_reduce_extreme {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (hL : ∀ e, α e ∈ L ∧ β e ∈ L) (S : Set (Finset E))
    (h : ∀ x ∈ (epQ α β L).extremePoints ℝ, x ∈ convexHull ℝ (epInd '' S)) :
    epQ α β L ⊆ convexHull ℝ (epInd '' S) := by
  have hfin : (epInd '' S : Set (E → ℝ)).Finite := Set.Finite.image _ (Set.toFinite S)
  have hclosed : IsClosed (convexHull ℝ (epInd '' S : Set (E → ℝ))) :=
    (Set.Finite.isCompact_convexHull (𝕜 := ℝ) hfin).isClosed
  rw [← closure_convexHull_extremePoints (epQ_compact α β L hL) (epQ_convex α β L)]
  exact closure_minimal (convexHull_min h (convex_convexHull ℝ _)) hclosed

open Classical in
/-- Contraction of `T` to its element `t₀`. -/
noncomputable def epRho {W : Type*} (T : Finset W) (t₀ : W) : W → W :=
  fun w => if w ∈ T then t₀ else w

open Classical in
/-- The preimage of a vertex set of the contracted graph. -/
noncomputable def epLift {W : Type*} (T : Finset W) (t₀ : W) (T' : Finset W) : Finset W :=
  if t₀ ∈ T' then T' ∪ T else T'

open Classical in
/-- The vertex set of the contracted graph. -/
noncomputable def epL' {W : Type*} (L T : Finset W) (t₀ : W) : Finset W := insert t₀ (L \ T)

open Classical in
/-- The weight vector on the contracted graph: new loops get weight `0`. -/
noncomputable def epX' {W E : Type*} (α β : E → W) (T : Finset W) (t₀ : W) (x : E → ℝ) :
    E → ℝ :=
  fun e => if epRho T t₀ (α e) = epRho T t₀ (β e) then 0 else x e

lemma epRho_mem {W : Type*} (L T : Finset W) (t₀ : W) (ht₀ : t₀ ∈ T) (T' : Finset W)
    (hT' : T' ⊆ epL' L T t₀) (w : W) : epRho T t₀ w ∈ T' ↔ w ∈ epLift T t₀ T' := by
  classical
  unfold epRho epLift
  by_cases hw : w ∈ T
  · rw [if_pos hw]
    by_cases h : t₀ ∈ T'
    · rw [if_pos h]; simp [h, hw]
    · rw [if_neg h]
      refine ⟨fun h' => absurd h' h, fun h' => ?_⟩
      have := hT' h'
      rw [epL', Finset.mem_insert, Finset.mem_sdiff] at this
      rcases this with rfl | ⟨-, h2⟩
      · exact h'
      · exact absurd hw h2
  · rw [if_neg hw]
    by_cases h : t₀ ∈ T'
    · rw [if_pos h]; simp [hw]
    · rw [if_neg h]

lemma epCross_contract {W E : Type*} (α β : E → W) (L T : Finset W) (t₀ : W) (ht₀ : t₀ ∈ T)
    (T' : Finset W) (hT' : T' ⊆ epL' L T t₀) (e : E) :
    epCross (fun e => epRho T t₀ (α e)) (fun e => epRho T t₀ (β e)) T' e ↔
      epCross α β (epLift T t₀ T') e := by
  unfold epCross
  simp only [epRho_mem L T t₀ ht₀ T' hT']

lemma epLift_subset {W : Type*} (L T : Finset W) (t₀ : W) (hT : T ⊆ L) (ht₀ : t₀ ∈ T)
    (T' : Finset W)
    (hT' : T' ⊆ epL' L T t₀) : epLift T t₀ T' ⊆ L := by
  classical
  have h1 : T' ⊆ L := by
    intro w hw
    have := hT' hw
    rw [epL', Finset.mem_insert, Finset.mem_sdiff] at this
    rcases this with rfl | ⟨h, -⟩
    · exact hT ht₀
    · exact h
  unfold epLift
  split_ifs
  · exact Finset.union_subset h1 hT
  · exact h1

lemma epLift_odd {W : Type*} (L T : Finset W) (t₀ : W) (ht₀ : t₀ ∈ T) (hodd : Odd T.card)
    (T' : Finset W) (hT' : T' ⊆ epL' L T t₀) (h : Odd T'.card) :
    Odd (epLift T t₀ T').card := by
  classical
  unfold epLift
  split_ifs with h0
  · have hdisj : Disjoint (T'.erase t₀) T := by
      rw [Finset.disjoint_left]
      intro w hw hwT
      have := hT' (Finset.mem_of_mem_erase hw)
      rw [epL', Finset.mem_insert, Finset.mem_sdiff] at this
      rcases this with rfl | ⟨-, h2⟩
      · exact (Finset.ne_of_mem_erase hw) rfl
      · exact h2 hwT
    have heq : T' ∪ T = T'.erase t₀ ∪ T := by
      ext w
      simp only [Finset.mem_union, Finset.mem_erase]
      constructor
      · rintro (h1 | h1)
        · by_cases hw : w = t₀
          · right; rw [hw]; exact ht₀
          · left; exact ⟨hw, h1⟩
        · right; exact h1
      · rintro (h1 | h1)
        · left; exact h1.2
        · right; exact h1
    rw [heq, Finset.card_union_of_disjoint hdisj, Finset.card_erase_of_mem h0]
    obtain ⟨a, ha⟩ := h
    obtain ⟨b, hb⟩ := hodd
    exact ⟨a + b, by omega⟩
  · exact h

lemma epLift_singleton_t₀ {W : Type*} (T : Finset W) (t₀ : W) (ht₀ : t₀ ∈ T) :
    epLift T t₀ {t₀} = T := by
  classical
  unfold epLift
  rw [if_pos (Finset.mem_singleton_self _)]
  ext w
  simp only [Finset.mem_union, Finset.mem_singleton]
  exact ⟨fun h => h.elim (fun h => h ▸ ht₀) id, Or.inr⟩

lemma epLift_singleton_ne {W : Type*} (T : Finset W) (t₀ c : W) (hc : c ≠ t₀) :
    epLift T t₀ {c} = {c} := by
  classical
  unfold epLift
  rw [if_neg (fun h => hc (Finset.mem_singleton.mp h).symm)]

/-- The sum of the contracted weights over a cut of the contracted graph. -/
lemma epX'_sum_cut {W E : Type*} [Fintype E] (α β : E → W) (L T : Finset W) (t₀ : W)
    (ht₀ : t₀ ∈ T) (x : E → ℝ) (T' : Finset W) (hT' : T' ⊆ epL' L T t₀) :
    ∑ e ∈ epCut (fun e => epRho T t₀ (α e)) (fun e => epRho T t₀ (β e)) T', epX' α β T t₀ x e =
      ∑ e ∈ epCut α β (epLift T t₀ T'), x e := by
  classical
  have hcut : epCut (fun e => epRho T t₀ (α e)) (fun e => epRho T t₀ (β e)) T' =
      epCut α β (epLift T t₀ T') := by
    ext e
    rw [mem_epCut, mem_epCut, epCross_contract α β L T t₀ ht₀ T' hT']
  rw [hcut]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [mem_epCut, ← epCross_contract α β L T t₀ ht₀ T' hT'] at he
  unfold epX'
  rw [if_neg]
  intro heq
  unfold epCross at he
  simp only [heq] at he
  tauto

/-- Contracting a tight odd set maps the polytope into the polytope of the contraction. -/
lemma ep_contract_mem {W E : Type*} [Fintype E] (α β : E → W) (L T : Finset W) (t₀ : W)
    (hT : T ⊆ L) (ht₀ : t₀ ∈ T) (hodd : Odd T.card) (x : E → ℝ) (hx : x ∈ epQ α β L)
    (htight : ∑ e ∈ epCut α β T, x e = 1) :
    epX' α β T t₀ x ∈ epQ (fun e => epRho T t₀ (α e)) (fun e => epRho T t₀ (β e))
      (epL' L T t₀) := by
  classical
  obtain ⟨h0, hloop, hdeg, hoddc⟩ := hx
  refine ⟨fun e => ?_, fun e he => ?_, fun c hc => ?_, fun T' hT' hT'odd => ?_⟩
  · unfold epX'; split_ifs
    · exact le_refl _
    · exact h0 e
  · unfold epX'; rw [if_pos he]
  · rw [epX'_sum_cut α β L T t₀ ht₀ x {c} (Finset.singleton_subset_iff.mpr hc)]
    by_cases hct : c = t₀
    · rw [hct, epLift_singleton_t₀ T t₀ ht₀]; exact htight
    · rw [epLift_singleton_ne T t₀ c hct]
      rw [epL', Finset.mem_insert, Finset.mem_sdiff] at hc
      rcases hc with h | ⟨h, -⟩
      · exact absurd h hct
      · exact hdeg c h
  · rw [epX'_sum_cut α β L T t₀ ht₀ x T' hT']
    exact hoddc _ (epLift_subset L T t₀ hT ht₀ T' hT') (epLift_odd L T t₀ ht₀ hodd T' hT' hT'odd)

lemma epL'_card {W : Type*} (L T : Finset W) (t₀ : W) (hT : T ⊆ L) (ht₀ : t₀ ∈ T) :
    (epL' L T t₀).card = L.card - T.card + 1 := by
  classical
  unfold epL'
  rw [Finset.card_insert_of_notMem (by simp [ht₀]), Finset.card_sdiff_of_subset hT]

lemma epRho_mem_L' {W : Type*} (L T : Finset W) (t₀ : W) (w : W) (hw : w ∈ L) :
    epRho T t₀ w ∈ epL' L T t₀ := by
  classical
  unfold epRho epL'
  split_ifs with h
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨hw, h⟩)

lemma epX'_eq {W E : Type*} (α β : E → W) (T : Finset W) (t₀ : W) (ht₀ : t₀ ∈ T) (x : E → ℝ)
    (e : E) (h : ¬(α e ∈ T ∧ β e ∈ T)) (hloop : α e = β e → x e = 0) :
    epX' α β T t₀ x e = x e := by
  classical
  unfold epX'
  by_cases hl : α e = β e
  · rw [if_pos (by rw [hl]), hloop hl]
  · rw [if_neg]
    intro h1
    unfold epRho at h1
    by_cases ha : α e ∈ T <;> by_cases hb : β e ∈ T
    · exact h ⟨ha, hb⟩
    · rw [if_pos ha, if_neg hb] at h1; exact hb (h1 ▸ ht₀)
    · rw [if_neg ha, if_pos hb] at h1; exact ha (h1 ▸ ht₀)
    · rw [if_neg ha, if_neg hb] at h1; exact hl h1

lemma epCross_sdiff {W E : Type*} (α β : E → W) (L T U : Finset W)
    (hU : ∀ w, w ∈ U ↔ w ∈ L ∧ w ∉ T)
    (hL : ∀ e, α e ∈ L ∧ β e ∈ L) (e : E) : epCross α β U e ↔ epCross α β T e := by
  unfold epCross
  simp only [hU, (hL e).1, (hL e).2, true_and]
  tauto

lemma epPM_contract_noloop {W E : Type*} (α β : E → W) (L T : Finset W) (t₀ : W)
    {M : Finset E} (hM : M ∈ epPM (fun e => epRho T t₀ (α e)) (fun e => epRho T t₀ (β e))
      (epL' L T t₀)) {e : E} (he : e ∈ M) : α e ≠ β e ∧ ¬(α e ∈ T ∧ β e ∈ T) := by
  classical
  have := hM.1 e he
  constructor
  · intro h; exact this (by simp only [h])
  · rintro ⟨h1, h2⟩; exact this (by simp only [epRho, if_pos h1, if_pos h2])

lemma epPM_contract_cut {W E : Type*} (α β : E → W) (L T : Finset W) (t₀ : W) (ht₀ : t₀ ∈ T)
    {M : Finset E} (hM : M ∈ epPM (fun e => epRho T t₀ (α e)) (fun e => epRho T t₀ (β e))
      (epL' L T t₀)) : ∃! f, f ∈ M ∧ epCross α β T f := by
  classical
  have h := hM.2 t₀ (by unfold epL'; exact Finset.mem_insert_self _ _)
  have hsub : ({t₀} : Finset W) ⊆ epL' L T t₀ := by
    unfold epL'; exact Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)
  simpa only [epCross_contract α β L T t₀ ht₀ {t₀} hsub, epLift_singleton_t₀ T t₀ ht₀] using h

lemma epPM_contract_vertex {W E : Type*} (α β : E → W) (L T : Finset W) (t₀ : W) (ht₀ : t₀ ∈ T)
    {M : Finset E} (hM : M ∈ epPM (fun e => epRho T t₀ (α e)) (fun e => epRho T t₀ (β e))
      (epL' L T t₀)) (c : W) (hc : c ∈ L) (hcT : c ∉ T) :
    ∃! e, e ∈ M ∧ epCross α β {c} e := by
  classical
  have hc' : c ∈ epL' L T t₀ := by
    unfold epL'; exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨hc, hcT⟩)
  have h := hM.2 c hc'
  have hne : c ≠ t₀ := fun h => hcT (h ▸ ht₀)
  simpa only [epCross_contract α β L T t₀ ht₀ {c} (Finset.singleton_subset_iff.mpr hc'),
    epLift_singleton_ne T t₀ c hne] using h

/-- An edge of a matching of the contraction that meets a vertex of `T` crosses `T`. -/
lemma epPM_contract_touch {W E : Type*} (α β : E → W) (L T : Finset W) (t₀ : W)
    {M : Finset E} (hM : M ∈ epPM (fun e => epRho T t₀ (α e)) (fun e => epRho T t₀ (β e))
      (epL' L T t₀)) {e : E} (he : e ∈ M) (c : W) (hc : c ∈ T)
    (hcross : epCross α β {c} e) : epCross α β T e := by
  have h := (epPM_contract_noloop α β L T t₀ hM he).2
  rw [epCross_singleton] at hcross
  unfold epCross
  rcases hcross with ⟨h1, -⟩ | ⟨-, h2⟩
  · left; exact ⟨h1 ▸ hc, fun hb => h ⟨h1 ▸ hc, hb⟩⟩
  · right; exact ⟨fun ha => h ⟨ha, h2 ▸ hc⟩, h2 ▸ hc⟩

/-- Uniqueness in a union, used for gluing. -/
lemma ep_glue_unique {E : Type*} [DecidableEq E] (P : E → Prop) (A B : Finset E) (f : E)
    (hf : f ∈ A) (hA : ∃! e, e ∈ A ∧ P e) (hB : ∀ e ∈ B, P e → e = f) :
    ∃! e, e ∈ A ∪ B ∧ P e := by
  obtain ⟨e₁, ⟨h1, h2⟩, huniq⟩ := hA
  refine ⟨e₁, ⟨Finset.mem_union_left _ h1, h2⟩, ?_⟩
  rintro e ⟨he, hP⟩
  rcases Finset.mem_union.mp he with h | h
  · exact huniq e ⟨h, hP⟩
  · have := hB e h hP
    exact huniq e ⟨this ▸ hf, hP⟩

/-- Gluing matchings of the two contractions along the common cut edge. -/
lemma ep_glue_mem {W E : Type*} [DecidableEq E] (α β : E → W) (L T U : Finset W) (t₀ s₀ : W)
    (hL : ∀ e, α e ∈ L ∧ β e ∈ L) (ht₀ : t₀ ∈ T) (hU : ∀ w, w ∈ U ↔ w ∈ L ∧ w ∉ T) (hs₀ : s₀ ∈ U)
    {M₁ M₂ : Finset E}
    (hM₁ : M₁ ∈ epPM (fun e => epRho T t₀ (α e)) (fun e => epRho T t₀ (β e)) (epL' L T t₀))
    (hM₂ : M₂ ∈ epPM (fun e => epRho U s₀ (α e)) (fun e => epRho U s₀ (β e))
      (epL' L U s₀))
    (f : E) (hf₁ : f ∈ M₁) (hf₂ : f ∈ M₂) (hfc : epCross α β T f) :
    M₁ ∪ M₂ ∈ epPM α β L := by
  have hcut₁ := epPM_contract_cut α β L T t₀ ht₀ hM₁
  have hcut₂ := epPM_contract_cut α β L U s₀ hs₀ hM₂
  simp only [epCross_sdiff α β L T U hU hL] at hcut₂
  refine ⟨fun e he => ?_, fun c hc => ?_⟩
  · rcases Finset.mem_union.mp he with h | h
    · exact (epPM_contract_noloop α β L T t₀ hM₁ h).1
    · exact (epPM_contract_noloop α β L U s₀ hM₂ h).1
  · by_cases hcT : c ∈ T
    · have hc' : c ∉ U := fun h => ((hU c).mp h).2 hcT
      rw [Finset.union_comm]
      refine ep_glue_unique _ M₂ M₁ f hf₂
        (epPM_contract_vertex α β L U s₀ hs₀ hM₂ c hc hc') ?_
      intro e he hcross
      have h1 := epPM_contract_touch α β L T t₀ hM₁ he c hcT hcross
      exact hcut₁.unique ⟨he, h1⟩ ⟨hf₁, hfc⟩
    · have hc' : c ∈ U := (hU c).mpr ⟨hc, hcT⟩
      refine ep_glue_unique _ M₁ M₂ f hf₁ (epPM_contract_vertex α β L T t₀ ht₀ hM₁ c hc hcT) ?_
      intro e he hcross
      have h1 := epPM_contract_touch α β L U s₀ hM₂ he c hc' hcross
      rw [epCross_sdiff α β L T U hU hL] at h1
      exact hcut₂.unique ⟨he, h1⟩ ⟨hf₂, hfc⟩

/-- For a valid pair, membership of an edge not inside `T` is decided by `M₁`. -/
lemma ep_glue_ind_outside {W E : Type*} [DecidableEq E] (α β : E → W) (L T U : Finset W)
    (t₀ s₀ : W) (hL : ∀ e, α e ∈ L ∧ β e ∈ L) (hU : ∀ w, w ∈ U ↔ w ∈ L ∧ w ∉ T) (hs₀ : s₀ ∈ U)
    {M₁ M₂ : Finset E}
    (hM₂ : M₂ ∈ epPM (fun e => epRho U s₀ (α e)) (fun e => epRho U s₀ (β e))
      (epL' L U s₀))
    (f : E) (hf₁ : f ∈ M₁) (hf₂ : f ∈ M₂) (hfc : epCross α β T f) (e : E)
    (he : ¬(α e ∈ T ∧ β e ∈ T)) : epInd (M₁ ∪ M₂) e = epInd M₁ e := by
  have hcut₂ := epPM_contract_cut α β L U s₀ hs₀ hM₂
  simp only [epCross_sdiff α β L T U hU hL] at hcut₂
  have key : e ∈ M₂ → e ∈ M₁ := by
    intro h
    have hn := (epPM_contract_noloop α β L U s₀ hM₂ h).2
    simp only [hU, (hL e).1, (hL e).2, true_and] at hn
    have hc : epCross α β T e := by unfold epCross; tauto
    exact (hcut₂.unique ⟨h, hc⟩ ⟨hf₂, hfc⟩) ▸ hf₁
  unfold epInd
  by_cases h1 : e ∈ M₁
  · rw [if_pos (Finset.mem_union_left _ h1), if_pos h1]
  · rw [if_neg h1, if_neg]
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact h1 h
    · exact h1 (key h)

/-- For a valid pair, membership of an edge inside `T` is decided by `M₂`. -/
lemma ep_glue_ind_inside {W E : Type*} [DecidableEq E] (α β : E → W) (L T : Finset W)
    (t₀ : W) {M₁ M₂ : Finset E}
    (hM₁ : M₁ ∈ epPM (fun e => epRho T t₀ (α e)) (fun e => epRho T t₀ (β e)) (epL' L T t₀))
    (e : E) (he : α e ∈ T ∧ β e ∈ T) : epInd (M₁ ∪ M₂) e = epInd M₂ e := by
  have h1 : e ∉ M₁ := fun h => (epPM_contract_noloop α β L T t₀ hM₁ h).2 he
  unfold epInd
  by_cases h2 : e ∈ M₂
  · rw [if_pos (Finset.mem_union_right _ h2), if_pos h2]
  · rw [if_neg h2, if_neg]
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact h1 h
    · exact h2 h

/-- The inner sum of the gluing weights is `1`. -/
lemma ep_glue_inner {E : Type*} [Fintype E] [DecidableEq E] (w' : Finset E → ℝ) (x : E → ℝ)
    (C : E → Prop) [DecidablePred C] (M : Finset E) (f₀ : E) (hf₀M : f₀ ∈ M) (hf₀C : C f₀)
    (huniq : ∀ f ∈ M, C f → f = f₀) (hy : x f₀ = ∑ M', w' M' * epInd M' f₀) (hx0 : x f₀ ≠ 0) :
    ∑ M', ∑ f, (if f ∈ M ∧ f ∈ M' ∧ C f then w' M' / x f else 0) = 1 := by
  have h1 : ∀ M' : Finset E, ∑ f, (if f ∈ M ∧ f ∈ M' ∧ C f then w' M' / x f else 0) =
      w' M' * epInd M' f₀ / x f₀ := by
    intro M'
    rw [Finset.sum_eq_single f₀]
    · unfold epInd
      by_cases h : f₀ ∈ M'
      · rw [if_pos ⟨hf₀M, h, hf₀C⟩, if_pos h, mul_one]
      · rw [if_neg (fun h' => h h'.2.1), if_neg h, mul_zero, zero_div]
    · intro f _ hf
      rw [if_neg]
      rintro ⟨h1, -, h3⟩
      exact hf (huniq f h1 h3)
    · intro h; exact absurd (Finset.mem_univ _) h
  simp only [h1]
  rw [← Finset.sum_div, ← hy, div_self hx0]

/-- Case A of Edmonds' theorem: gluing convex combinations over a tight odd cut. -/
lemma ep_glue {W E : Type*} [Fintype E] (α β : E → W) (L T U : Finset W) (t₀ s₀ : W)
    (hU : ∀ w, w ∈ U ↔ w ∈ L ∧ w ∉ T) (hL : ∀ e, α e ∈ L ∧ β e ∈ L) (ht₀ : t₀ ∈ T)
    (hs₀ : s₀ ∈ U) (x : E → ℝ) (hx : x ∈ epQ α β L)
    (h1 : epX' α β T t₀ x ∈ convexHull ℝ (epInd '' epPM (fun e => epRho T t₀ (α e))
      (fun e => epRho T t₀ (β e)) (epL' L T t₀)))
    (h2 : epX' α β U s₀ x ∈ convexHull ℝ (epInd '' epPM (fun e => epRho U s₀ (α e))
      (fun e => epRho U s₀ (β e)) (epL' L U s₀))) :
    x ∈ convexHull ℝ (epInd '' epPM α β L) := by
  classical
  obtain ⟨w₁, hw₁, hS₁, hsum₁, hx₁⟩ := ep_hull_repr _ _ h1
  obtain ⟨w₂, hw₂, hS₂, hsum₂, hx₂⟩ := ep_hull_repr _ _ h2
  have hx1cross : ∀ f, epCross α β T f → epX' α β T t₀ x f = x f := by
    intro f hf
    refine epX'_eq α β T t₀ ht₀ x f ?_ (hx.2.1 f)
    unfold epCross at hf; tauto
  have hx2cross : ∀ f, epCross α β T f → epX' α β U s₀ x f = x f := by
    intro f hf
    refine epX'_eq α β U s₀ hs₀ x f ?_ (hx.2.1 f)
    rw [← epCross_sdiff α β L T U hU hL] at hf
    unfold epCross at hf; tauto
  have hcut₂ : ∀ M₂, w₂ M₂ ≠ 0 → ∃! f, f ∈ M₂ ∧ epCross α β T f := by
    intro M₂ h
    have := epPM_contract_cut α β L U s₀ hs₀ (hS₂ M₂ h)
    simpa only [epCross_sdiff α β L T U hU hL] using this
  have hpos₁ : ∀ M₁ f, w₁ M₁ ≠ 0 → f ∈ M₁ → epCross α β T f → x f ≠ 0 := by
    intro M₁ f h hf hc
    have h0 : 0 < w₁ M₁ := lt_of_le_of_ne (hw₁ M₁) (Ne.symm h)
    have : w₁ M₁ * epInd M₁ f ≤ ∑ M, w₁ M * epInd M f :=
      Finset.single_le_sum (f := fun M => w₁ M * epInd M f)
        (fun M _ => mul_nonneg (hw₁ M) (by unfold epInd; split_ifs <;> norm_num))
        (Finset.mem_univ M₁)
    rw [← hx₁ f, hx1cross f hc] at this
    have h1 : epInd M₁ f = 1 := by unfold epInd; rw [if_pos hf]
    rw [h1, mul_one] at this
    linarith
  have hpos₂ : ∀ M₂ f, w₂ M₂ ≠ 0 → f ∈ M₂ → epCross α β T f → x f ≠ 0 := by
    intro M₂ f h hf hc
    have h0 : 0 < w₂ M₂ := lt_of_le_of_ne (hw₂ M₂) (Ne.symm h)
    have : w₂ M₂ * epInd M₂ f ≤ ∑ M, w₂ M * epInd M f :=
      Finset.single_le_sum (f := fun M => w₂ M * epInd M f)
        (fun M _ => mul_nonneg (hw₂ M) (by unfold epInd; split_ifs <;> norm_num))
        (Finset.mem_univ M₂)
    rw [← hx₂ f, hx2cross f hc] at this
    have h1 : epInd M₂ f = 1 := by unfold epInd; rw [if_pos hf]
    rw [h1, mul_one] at this
    linarith
  have inner₁ : ∀ M₁, w₁ M₁ ≠ 0 →
      ∑ M₂, ∑ f, (if f ∈ M₁ ∧ f ∈ M₂ ∧ epCross α β T f then w₂ M₂ / x f else 0) = 1 := by
    intro M₁ h
    obtain ⟨f₀, ⟨hf1, hf2⟩, huniq⟩ := epPM_contract_cut α β L T t₀ ht₀ (hS₁ M₁ h)
    exact ep_glue_inner w₂ x (fun f => epCross α β T f) M₁ f₀ hf1 hf2
      (fun f hf hc => huniq f ⟨hf, hc⟩) (by rw [← hx₂ f₀, hx2cross f₀ hf2])
      (hpos₁ M₁ f₀ h hf1 hf2)
  have inner₂ : ∀ M₂, w₂ M₂ ≠ 0 →
      ∑ M₁, ∑ f, (if f ∈ M₂ ∧ f ∈ M₁ ∧ epCross α β T f then w₁ M₁ / x f else 0) = 1 := by
    intro M₂ h
    obtain ⟨f₀, ⟨hf1, hf2⟩, huniq⟩ := hcut₂ M₂ h
    exact ep_glue_inner w₁ x (fun f => epCross α β T f) M₂ f₀ hf1 hf2
      (fun f hf hc => huniq f ⟨hf, hc⟩) (by rw [← hx₁ f₀, hx1cross f₀ hf2])
      (hpos₂ M₂ f₀ h hf1 hf2)
  refine ep_hull_of_family (ι := Finset E × Finset E × E) (epPM α β L)
    (fun i => if i.2.2 ∈ i.1 ∧ i.2.2 ∈ i.2.1 ∧ epCross α β T i.2.2 then
      w₁ i.1 * w₂ i.2.1 / x i.2.2 else 0) (fun i => i.1 ∪ i.2.1) ?_ ?_ ?_ x ?_
  · rintro ⟨M₁, M₂, f⟩
    dsimp only
    split_ifs
    · exact div_nonneg (mul_nonneg (hw₁ M₁) (hw₂ M₂)) (hx.1 f)
    · exact le_refl _
  · rintro ⟨M₁, M₂, f⟩ hne
    dsimp only at hne ⊢
    by_cases hc : f ∈ M₁ ∧ f ∈ M₂ ∧ epCross α β T f
    · rw [if_pos hc] at hne
      have h1 : w₁ M₁ ≠ 0 := fun h => hne (by rw [h, zero_mul, zero_div])
      have h2 : w₂ M₂ ≠ 0 := fun h => hne (by rw [h, mul_zero, zero_div])
      exact ep_glue_mem α β L T U t₀ s₀ hL ht₀ hU hs₀ (hS₁ M₁ h1) (hS₂ M₂ h2) f hc.1 hc.2.1
        hc.2.2
    · rw [if_neg hc] at hne; exact absurd rfl hne
  · rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type]
    have : ∀ M₁ : Finset E, ∑ M₂ : Finset E, ∑ f : E,
        (if f ∈ M₁ ∧ f ∈ M₂ ∧ epCross α β T f then w₁ M₁ * w₂ M₂ / x f else 0) = w₁ M₁ := by
      intro M₁
      by_cases h : w₁ M₁ = 0
      · simp [h]
      · have e1 : ∀ (M₂ : Finset E) (f : E),
            (if f ∈ M₁ ∧ f ∈ M₂ ∧ epCross α β T f then w₁ M₁ * w₂ M₂ / x f else 0) =
              w₁ M₁ * (if f ∈ M₁ ∧ f ∈ M₂ ∧ epCross α β T f then w₂ M₂ / x f else 0) := by
          intro M₂ f; split_ifs <;> ring
        simp only [e1, ← Finset.mul_sum]
        rw [inner₁ M₁ h, mul_one]
    simp only [this]
    exact hsum₁
  · intro e
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type]
    by_cases hin : α e ∈ T ∧ β e ∈ T
    · -- edges inside `T` are governed by `M₂`
      have hxe : x e = ∑ M₂, w₂ M₂ * epInd M₂ e := by
        rw [← hx₂ e]
        refine (epX'_eq α β U s₀ hs₀ x e ?_ (hx.2.1 e)).symm
        rintro ⟨h1, -⟩
        exact ((hU _).mp h1).2 hin.1
      have e1 : ∀ (M₁ M₂ : Finset E) (f : E),
          (if f ∈ M₁ ∧ f ∈ M₂ ∧ epCross α β T f then w₁ M₁ * w₂ M₂ / x f else 0) *
            epInd (M₁ ∪ M₂) e = w₂ M₂ * epInd M₂ e *
              (if f ∈ M₂ ∧ f ∈ M₁ ∧ epCross α β T f then w₁ M₁ / x f else 0) := by
        intro M₁ M₂ f
        by_cases hc : f ∈ M₁ ∧ f ∈ M₂ ∧ epCross α β T f
        · rw [if_pos hc, if_pos ⟨hc.2.1, hc.1, hc.2.2⟩]
          by_cases h : w₁ M₁ = 0
          · rw [h]; ring
          · rw [ep_glue_ind_inside α β L T t₀ (hS₁ M₁ h) e hin]; ring
        · rw [if_neg hc, if_neg (fun h => hc ⟨h.2.1, h.1, h.2.2⟩)]; ring
      simp only [e1]
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum]
      rw [hxe]
      refine Finset.sum_congr rfl fun M₂ _ => ?_
      by_cases h : w₂ M₂ = 0
      · rw [h]; ring
      · rw [inner₂ M₂ h, mul_one]
    · have hxe : x e = ∑ M₁, w₁ M₁ * epInd M₁ e := by
        rw [← hx₁ e]
        exact (epX'_eq α β T t₀ ht₀ x e hin (hx.2.1 e)).symm
      have e1 : ∀ (M₁ M₂ : Finset E) (f : E),
          (if f ∈ M₁ ∧ f ∈ M₂ ∧ epCross α β T f then w₁ M₁ * w₂ M₂ / x f else 0) *
            epInd (M₁ ∪ M₂) e = w₁ M₁ * epInd M₁ e *
              (if f ∈ M₁ ∧ f ∈ M₂ ∧ epCross α β T f then w₂ M₂ / x f else 0) := by
        intro M₁ M₂ f
        by_cases hc : f ∈ M₁ ∧ f ∈ M₂ ∧ epCross α β T f
        · rw [if_pos hc, if_pos hc]
          by_cases h : w₂ M₂ = 0
          · rw [h]; ring
          · rw [ep_glue_ind_outside α β L T U t₀ s₀ hL hU hs₀ (hS₂ M₂ h) f hc.1 hc.2.1 hc.2.2 e
              hin]
            ring
        · simp only [if_neg hc]; ring
      simp only [e1, ← Finset.mul_sum]
      rw [hxe]
      refine Finset.sum_congr rfl fun M₁ _ => ?_
      by_cases h : w₁ M₁ = 0
      · rw [h]; ring
      · rw [inner₁ M₁ h, mul_one]

/-- If `x` is in the polytope then `|L|` is even. -/
lemma epQ_even {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (hL : ∀ e, α e ∈ L ∧ β e ∈ L) {x : E → ℝ} (hx : x ∈ epQ α β L) : Even L.card := by
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  have h := hx.2.2.2 L (Finset.Subset.refl L) hodd
  have hempty : epCut α β L = ∅ := by
    ext e
    rw [mem_epCut]
    unfold epCross
    simp [(hL e).1, (hL e).2]
  rw [hempty, Finset.sum_empty] at h
  linarith

/-- No "nontrivial" tight odd set: the hypothesis of case B. -/
def epNoTight {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (x : E → ℝ) : Prop :=
  ∀ T ⊆ L, Odd T.card → 3 ≤ T.card → T.card + 3 ≤ L.card → 1 < ∑ e ∈ epCut α β T, x e

/-- Perturbation lemma: at an extreme point without nontrivial tight odd sets, a direction that
is supported on the fractional edges and has zero vertex sums vanishes. -/
lemma ep_perturb {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (hL : ∀ e, α e ∈ L ∧ β e ∈ L) {x : E → ℝ} (hx : x ∈ (epQ α β L).extremePoints ℝ)
    (hB : epNoTight α β L x) (d : E → ℝ) (hd0 : ∀ e, ¬(0 < x e ∧ x e < 1) → d e = 0)
    (hdv : ∀ c ∈ L, ∑ e ∈ epCut α β {c}, d e = 0) : d = 0 := by
  classical
  have hxQ := hx.1
  obtain ⟨h0, hloop, hdeg, hoddc⟩ := hxQ
  have heven := epQ_even α β L hL hx.1
  -- the good set of parameters
  have hP : ∀ᶠ t : ℝ in nhds 0, (∀ e, 0 < x e → 0 < x e + t * d e) ∧
      ∀ T ∈ L.powerset, Odd T.card → 3 ≤ T.card → T.card + 3 ≤ L.card →
        1 < ∑ e ∈ epCut α β T, (x e + t * d e) := by
    refine Filter.Eventually.and ?_ ?_
    · rw [Filter.eventually_all]
      intro e
      by_cases he : 0 < x e
      · have hc : ContinuousAt (fun t : ℝ => x e + t * d e) 0 := by fun_prop
        have : (fun t : ℝ => x e + t * d e) 0 > 0 := by simpa using he
        exact (hc.eventually (lt_mem_nhds this)).mono fun t ht _ => ht
      · exact Filter.Eventually.of_forall fun t h => absurd h he
    · rw [Filter.eventually_all_finset]
      intro T hT
      by_cases hcond : Odd T.card ∧ 3 ≤ T.card ∧ T.card + 3 ≤ L.card
      · have hc : ContinuousAt (fun t : ℝ => ∑ e ∈ epCut α β T, (x e + t * d e)) 0 := by
          fun_prop
        have : (fun t : ℝ => ∑ e ∈ epCut α β T, (x e + t * d e)) 0 > 1 := by
          simpa using hB T (Finset.mem_powerset.mp hT) hcond.1 hcond.2.1 hcond.2.2
        exact (hc.eventually (lt_mem_nhds this)).mono fun t ht _ _ _ => ht
      · exact Filter.Eventually.of_forall fun t h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hcond
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hP
  -- membership in the polytope for good parameters
  have hmem : ∀ t : ℝ, ((∀ e, 0 < x e → 0 < x e + t * d e) ∧
      ∀ T ∈ L.powerset, Odd T.card → 3 ≤ T.card → T.card + 3 ≤ L.card →
        1 < ∑ e ∈ epCut α β T, (x e + t * d e)) → (fun e => x e + t * d e) ∈ epQ α β L := by
    rintro t ⟨hp, hT⟩
    have hsum : ∀ c ∈ L, ∑ e ∈ epCut α β {c}, (x e + t * d e) = 1 := by
      intro c hc
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hdv c hc, hdeg c hc]; ring
    refine ⟨fun e => ?_, fun e he => ?_, hsum, fun T hTL hTodd => ?_⟩
    · by_cases he : 0 < x e
      · exact (hp e he).le
      · show 0 ≤ x e + t * d e
        rw [hd0 e (fun h => he h.1)]; simpa using h0 e
    · show x e + t * d e = 0
      rw [hd0 e (fun h => by rw [hloop e he] at h; exact lt_irrefl _ h.1), hloop e he]; simp
    · by_cases h3 : 3 ≤ T.card
      · by_cases h4 : T.card + 3 ≤ L.card
        · exact (hT T (Finset.mem_powerset.mpr hTL) hTodd h3 h4).le
        · -- then `L \ T` is a single vertex
          have hle := Finset.card_le_card hTL
          have hcard : (L \ T).card = 1 := by
            rw [Finset.card_sdiff_of_subset hTL]
            obtain ⟨a, ha⟩ := hTodd
            obtain ⟨b, hb⟩ := heven
            omega
          obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcard
          have hcL : c ∈ L := by
            have : c ∈ L \ T := by rw [hc]; exact Finset.mem_singleton_self c
            exact (Finset.mem_sdiff.mp this).1
          have hcut : epCut α β T = epCut α β {c} := by
            ext e
            rw [mem_epCut, mem_epCut, ← hc]
            exact (epCross_sdiff α β L T (L \ T) (fun w => Finset.mem_sdiff) hL e).symm
          rw [hcut, hsum c hcL]
      · have h1 : T.card = 1 := by
          obtain ⟨a, ha⟩ := hTodd; omega
        obtain ⟨c, rfl⟩ := Finset.card_eq_one.mp h1
        rw [hsum c (hTL (Finset.mem_singleton_self c))]
  have hplus := hmem (ε / 2) (hball (by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith))
  have hminus := hmem (-(ε / 2)) (hball (by
    rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos (by linarith)]; linarith))
  have hseg : x ∈ openSegment ℝ (fun e => x e + ε / 2 * d e) (fun e => x e + -(ε / 2) * d e) := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    funext e
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have := (mem_extremePoints.mp hx).2 _ hplus _ hminus hseg
  funext e
  have h1 := congrFun this.1 e
  simp only [Pi.zero_apply] at h1 ⊢
  have : ε / 2 * d e = 0 := by linarith
  exact (mul_eq_zero.mp this).resolve_left (by positivity)

lemma ep_cross_ends {W E : Type*} (α β : E → W) (e : E) (h : α e ≠ β e) (v : W) :
    epCross α β {v} e ↔ v = α e ∨ v = β e := by
  rw [epCross_singleton]
  constructor
  · rintro (⟨h1, -⟩ | ⟨-, h2⟩)
    · exact Or.inl h1.symm
    · exact Or.inr h2.symm
  · rintro (rfl | rfl)
    · exact Or.inl ⟨rfl, fun h' => h h'.symm⟩
    · exact Or.inr ⟨h, rfl⟩

open Classical in
/-- The fractional edges. -/
noncomputable def epF {E : Type*} [Fintype E] (x : E → ℝ) : Finset E :=
  Finset.univ.filter (fun e => 0 < x e ∧ x e < 1)

open Classical in
/-- The fractional edges at the vertex `c`. -/
noncomputable def epFc {W E : Type*} [Fintype E] (α β : E → W) (x : E → ℝ) (c : W) : Finset E :=
  (epF x).filter (epCross α β {c})

open Classical in
/-- The vertices meeting a fractional edge. -/
noncomputable def epW' {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (x : E → ℝ) :
    Finset W :=
  L.filter (fun c => (epFc α β x c).Nonempty)

lemma mem_epF {E : Type*} [Fintype E] (x : E → ℝ) (e : E) : e ∈ epF x ↔ 0 < x e ∧ x e < 1 := by
  classical
  simp [epF]

lemma mem_epFc {W E : Type*} [Fintype E] (α β : E → W) (x : E → ℝ) (c : W) (e : E) :
    e ∈ epFc α β x c ↔ (0 < x e ∧ x e < 1) ∧ epCross α β {c} e := by
  classical
  simp [epFc, mem_epF]

lemma mem_epW' {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (x : E → ℝ) (c : W) :
    c ∈ epW' α β L x ↔ c ∈ L ∧ (epFc α β x c).Nonempty := by
  classical
  simp [epW']

/-- A fractional edge at `c` forces the other edges at `c` to have small weight. -/
lemma ep_frac_le {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) {x : E → ℝ}
    (hx : x ∈ epQ α β L) (c : W) (hc : c ∈ L) (e g : E) (he : epCross α β {c} e)
    (hg : epCross α β {c} g) (hne : g ≠ e) : x g ≤ 1 - x e := by
  classical
  have h := hx.2.2.1 c hc
  have hsub : ({e, g} : Finset E) ⊆ epCut α β {c} := by
    intro f hf
    rw [Finset.mem_insert, Finset.mem_singleton] at hf
    rw [mem_epCut]
    rcases hf with rfl | rfl <;> assumption
  have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hx.1 i)
  rw [Finset.sum_pair (Ne.symm hne), h] at this
  linarith

/-- Every vertex meeting a fractional edge meets a second one. -/
lemma ep_frac_partner {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) {x : E → ℝ}
    (hx : x ∈ epQ α β L) (c : W) (hc : c ∈ L) (e : E) (he : e ∈ epFc α β x c) :
    ∃ e', e' ≠ e ∧ e' ∈ epFc α β x c := by
  classical
  rw [mem_epFc] at he
  obtain ⟨⟨h0, h1⟩, hcr⟩ := he
  have h := hx.2.2.1 c hc
  have hmem : e ∈ epCut α β {c} := (mem_epCut _ _ _ _).mpr hcr
  rw [← Finset.add_sum_erase _ _ hmem] at h
  have hpos : 0 < ∑ g ∈ (epCut α β {c}).erase e, x g := by linarith
  obtain ⟨g, hg, hgpos⟩ := Finset.exists_lt_of_sum_lt (f := fun _ => (0 : ℝ)) (by simpa using hpos)
  have hgne := Finset.ne_of_mem_erase hg
  have hgc : epCross α β {c} g := (mem_epCut _ _ _ _).mp (Finset.mem_of_mem_erase hg)
  have := ep_frac_le α β L hx c hc e g hcr hgc hgne
  exact ⟨g, hgne, (mem_epFc _ _ _ _ _).mpr ⟨⟨hgpos, by linarith⟩, hgc⟩⟩

lemma ep_deg_two_le {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) {x : E → ℝ}
    (hx : x ∈ epQ α β L) (c : W) (hc : c ∈ epW' α β L x) : 2 ≤ (epFc α β x c).card := by
  rw [mem_epW'] at hc
  obtain ⟨hcL, e, he⟩ := hc
  obtain ⟨e', hne, he'⟩ := ep_frac_partner α β L hx c hcL e he
  exact Finset.one_lt_card.mpr ⟨e', he', e, he, hne⟩

/-- Double counting of incidences between fractional edges and their vertices. -/
lemma ep_sum_deg {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (hL : ∀ e, α e ∈ L ∧ β e ∈ L) {x : E → ℝ} (hx : x ∈ epQ α β L) :
    ∑ c ∈ epW' α β L x, (epFc α β x c).card = 2 * (epF x).card := by
  classical
  have h1 := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := epW' α β L x) (t := epF x) (fun c e => epCross α β {c} e)
  have h2 : ∀ c ∈ epW' α β L x, (Finset.bipartiteAbove (fun c e => epCross α β {c} e) (epF x) c) =
      epFc α β x c := by
    intro c _
    rfl
  rw [Finset.sum_congr rfl (fun c hc => by rw [h2 c hc])] at h1
  rw [h1]
  have h3 : ∀ e ∈ epF x, (Finset.bipartiteBelow (fun c e => epCross α β {c} e)
      (epW' α β L x) e).card = 2 := by
    intro e he
    have hpos := ((mem_epF x e).mp he).1
    have hne : α e ≠ β e := fun h => by rw [hx.2.1 e h] at hpos; exact lt_irrefl _ hpos
    have heq : Finset.bipartiteBelow (fun c e => epCross α β {c} e) (epW' α β L x) e =
        {α e, β e} := by
      ext v
      rw [Finset.mem_bipartiteBelow, Finset.mem_insert, Finset.mem_singleton,
        ep_cross_ends α β e hne v, mem_epW']
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨⟨?_, e, (mem_epFc _ _ _ _ _).mpr ⟨(mem_epF x e).mp he,
          (ep_cross_ends α β e hne v).mpr h⟩⟩, h⟩
        rcases h with rfl | rfl
        · exact (hL e).1
        · exact (hL e).2
    rw [heq, Finset.card_pair hne]
  rw [Finset.sum_congr rfl h3, Finset.sum_const, smul_eq_mul, mul_comm]

/-- At an extreme point without nontrivial tight odd sets there are at most as many fractional
edges as vertices meeting them. -/
lemma ep_card_le {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (hL : ∀ e, α e ∈ L ∧ β e ∈ L) {x : E → ℝ} (hx : x ∈ (epQ α β L).extremePoints ℝ)
    (hB : epNoTight α β L x) : (epF x).card ≤ (epW' α β L x).card := by
  classical
  let A : Matrix {c // c ∈ epW' α β L x} {e // e ∈ epF x} ℝ :=
    fun c e => if epCross α β {c.1} e.1 then 1 else 0
  have hinj : Function.Injective A.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro g hg
    have hd := ep_perturb α β L hL hx hB (fun e => if h : e ∈ epF x then g ⟨e, h⟩ else 0)
      (fun e he => by rw [dif_neg (fun h => he ((mem_epF x e).mp h))]) (fun c hc => by
        have hsum : ∑ e ∈ epCut α β {c}, (if h : e ∈ epF x then g ⟨e, h⟩ else 0) =
            ∑ e ∈ epF x, (if epCross α β {c} e then (1 : ℝ) else 0) *
              (if h : e ∈ epF x then g ⟨e, h⟩ else 0) := by
          unfold epCut
          rw [Finset.sum_filter]
          rw [← Finset.sum_subset (Finset.subset_univ (epF x))]
          · exact Finset.sum_congr rfl fun e _ => by split_ifs <;> simp
          · intro e _ he
            rw [dif_neg he]; simp
        rw [hsum]
        by_cases hcW : c ∈ epW' α β L x
        · have := congrFun hg ⟨c, hcW⟩
          simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.zero_apply] at this
          rw [← Finset.sum_coe_sort (epF x)]
          refine Eq.trans (Finset.sum_congr rfl fun e _ => ?_) this
          rw [dif_pos e.2]
        · refine Finset.sum_eq_zero fun e he => ?_
          rw [if_neg, zero_mul]
          intro hcr
          exact hcW ((mem_epW' _ _ _ _ _).mpr ⟨hc, e, (mem_epFc _ _ _ _ _).mpr
            ⟨(mem_epF x e).mp he, hcr⟩⟩))
    funext e
    have := congrFun hd e.1
    simpa [dif_pos e.2] using this
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [Module.finrank_fintype_fun_eq_card] using this

/-- In case B every vertex meeting a fractional edge meets exactly two. -/
lemma ep_deg_eq_two {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (hL : ∀ e, α e ∈ L ∧ β e ∈ L) {x : E → ℝ} (hx : x ∈ (epQ α β L).extremePoints ℝ)
    (hB : epNoTight α β L x) (c : W) (hc : c ∈ epW' α β L x) : (epFc α β x c).card = 2 := by
  have h1 := ep_sum_deg α β L hL hx.1
  have h2 := ep_card_le α β L hL hx hB
  have h3 : ∀ c ∈ epW' α β L x, 2 ≤ (epFc α β x c).card := ep_deg_two_le α β L hx.1
  have h4 : ∑ c ∈ epW' α β L x, 2 = ∑ c ∈ epW' α β L x, (epFc α β x c).card := by
    refine le_antisymm (Finset.sum_le_sum h3) ?_
    rw [h1, Finset.sum_const, smul_eq_mul, mul_comm]
    exact Nat.mul_le_mul_right 2 h2
  exact ((Finset.sum_eq_sum_iff_of_le h3).mp h4 c hc).symm

lemma ep_other_end {W E : Type*} (α β : E → W) (e : E) (h : α e ≠ β e) (c : W)
    (hc : epCross α β {c} e) :
    ∃ a, a ≠ c ∧ (a = α e ∨ a = β e) ∧ ∀ v, epCross α β {v} e ↔ v = c ∨ v = a := by
  rcases (ep_cross_ends α β e h c).mp hc with rfl | rfl
  · exact ⟨β e, fun h' => h h'.symm, Or.inr rfl, fun v => ep_cross_ends α β e h v⟩
  · exact ⟨α e, h, Or.inl rfl, fun v => by rw [ep_cross_ends α β e h v]; tauto⟩

open Classical in
/-- A signed combination of fractional edges with zero vertex sums vanishes. -/
lemma ep_signed {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (hL : ∀ e, α e ∈ L ∧ β e ∈ L) {x : E → ℝ} (hx : x ∈ (epQ α β L).extremePoints ℝ)
    (hB : epNoTight α β L x) {ι : Type*} [Fintype ι] (g : ι → E) (s : ι → ℝ)
    (hg : ∀ i, g i ∈ epF x)
    (hv : ∀ v ∈ L, ∑ i, s i * (if epCross α β {v} (g i) then 1 else 0) = 0) (e : E) :
    ∑ i, (if g i = e then s i else 0) = 0 := by
  have hd := ep_perturb α β L hL hx hB (fun e => ∑ i, (if g i = e then s i else 0))
    (fun e he => by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [if_neg]
      intro h
      exact he ((mem_epF x e).mp (h ▸ hg i)))
    (fun c hc => by
      rw [Finset.sum_comm]
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (hv c hc)
      rw [Finset.sum_ite_eq]
      by_cases h : epCross α β {c} (g i)
      · rw [if_pos ((mem_epCut _ _ _ _).mpr h), if_pos h, mul_one]
      · rw [if_neg (fun h' => h ((mem_epCut _ _ _ _).mp h')), if_neg h, mul_zero])
  exact congrFun hd e

lemma ep_card_two_other {E : Type*} [DecidableEq E] (s : Finset E) (h : s.card = 2) (e : E)
    (he : e ∈ s) : ∃ e', e' ≠ e ∧ s = {e, e'} := by
  obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp h
  rw [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl
  · exact ⟨q, Ne.symm hpq, rfl⟩
  · exact ⟨p, hpq, Finset.pair_comm p e⟩

/-- A vertex with exactly two fractional edges. -/
lemma ep_vertex_two {W E : Type*} [Fintype E] [DecidableEq E] (α β : E → W) (L : Finset W)
    {x : E → ℝ} (hx : x ∈ epQ α β L) (v : W) (hv : v ∈ L) (p q : E) (hpq : p ≠ q)
    (hF : epFc α β x v = {p, q}) :
    x p + x q = 1 ∧ ∀ g, epCross α β {v} g → 0 < x g → g = p ∨ g = q := by
  have hp : p ∈ epFc α β x v := by rw [hF]; exact Finset.mem_insert_self _ _
  have hq : q ∈ epFc α β x v := by
    rw [hF]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  rw [mem_epFc] at hp hq
  have hpos : ∀ g, epCross α β {v} g → 0 < x g → g = p ∨ g = q := by
    intro g hg hgpos
    by_cases hgp : g = p
    · exact Or.inl hgp
    · have := ep_frac_le α β L hx v hv p g hp.2 hg hgp
      have hgF : g ∈ epFc α β x v := (mem_epFc _ _ _ _ _).mpr ⟨⟨hgpos, by linarith [hp.1.1]⟩, hg⟩
      rw [hF, Finset.mem_insert, Finset.mem_singleton] at hgF
      exact hgF
  refine ⟨?_, hpos⟩
  have h := hx.2.2.1 v hv
  have hsub : ({p, q} : Finset E) ⊆ epCut α β {v} := by
    intro f hf
    rw [Finset.mem_insert, Finset.mem_singleton] at hf
    rw [mem_epCut]
    rcases hf with rfl | rfl
    · exact hp.2
    · exact hq.2
  rw [← Finset.sum_subset hsub, Finset.sum_pair hpq] at h
  · exact h
  · intro g hg hgn
    by_contra hne
    have hgpos : 0 < x g := lt_of_le_of_ne (hx.1 g) (Ne.symm hne)
    have := hpos g ((mem_epCut _ _ _ _).mp hg) hgpos
    rw [Finset.mem_insert, Finset.mem_singleton] at hgn
    exact hgn this

open Classical in
/-- `ep_signed` for four signed edges. -/
lemma ep_signed4 {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (hL : ∀ e, α e ∈ L ∧ β e ∈ L) {x : E → ℝ} (hx : x ∈ (epQ α β L).extremePoints ℝ)
    (hB : epNoTight α β L x) (g₁ g₂ g₃ g₄ : E) (s₁ s₂ s₃ s₄ : ℝ)
    (h₁ : g₁ ∈ epF x) (h₂ : g₂ ∈ epF x) (h₃ : g₃ ∈ epF x) (h₄ : g₄ ∈ epF x)
    (hv : ∀ v ∈ L, s₁ * (if epCross α β {v} g₁ then 1 else 0) +
      s₂ * (if epCross α β {v} g₂ then 1 else 0) + s₃ * (if epCross α β {v} g₃ then 1 else 0) +
      s₄ * (if epCross α β {v} g₄ then 1 else 0) = 0) (e : E) :
    (if g₁ = e then s₁ else 0) + (if g₂ = e then s₂ else 0) + (if g₃ = e then s₃ else 0) +
      (if g₄ = e then s₄ else 0) = 0 := by
  have := ep_signed α β L hL hx hB ![g₁, g₂, g₃, g₄] ![s₁, s₂, s₃, s₄]
    (fun i => by fin_cases i <;> assumption)
    (fun v hv' => by
      rw [Fin.sum_univ_four]
      exact hv v hv') e
  rw [Fin.sum_univ_four] at this
  exact this

/-- In case B there are no fractional edges. -/
lemma ep_W'_empty {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (hL : ∀ e, α e ∈ L ∧ β e ∈ L) {x : E → ℝ} (hx : x ∈ (epQ α β L).extremePoints ℝ)
    (hB : epNoTight α β L x) : epW' α β L x = ∅ := by
  classical
  by_contra hne
  obtain ⟨c, hc⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  have hxQ := hx.1
  have hcL : c ∈ L := ((mem_epW' _ _ _ _ _).mp hc).1
  have hdeg := ep_deg_eq_two α β L hL hx hB
  obtain ⟨e₁, e₂, h12, hFc⟩ := Finset.card_eq_two.mp (hdeg c hc)
  have hF₁ : (0 < x e₁ ∧ x e₁ < 1) ∧ epCross α β {c} e₁ := by
    rw [← mem_epFc, hFc]; exact Finset.mem_insert_self _ _
  have hF₂ : (0 < x e₂ ∧ x e₂ < 1) ∧ epCross α β {c} e₂ := by
    rw [← mem_epFc, hFc]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hnl : ∀ e, 0 < x e → α e ≠ β e := fun e h heq => by
    rw [hxQ.2.1 e heq] at h; exact lt_irrefl _ h
  obtain ⟨a, hac, haend, H1⟩ := ep_other_end α β e₁ (hnl e₁ hF₁.1.1) c hF₁.2
  obtain ⟨b, hbc, hbend, H2⟩ := ep_other_end α β e₂ (hnl e₂ hF₂.1.1) c hF₂.2
  have haL : a ∈ L := by
    rcases haend with h | h
    · rw [h]; exact (hL e₁).1
    · rw [h]; exact (hL e₁).2
  have hbL : b ∈ L := by
    rcases hbend with h | h
    · rw [h]; exact (hL e₂).1
    · rw [h]; exact (hL e₂).2
  have hm₁ : e₁ ∈ epF x := (mem_epF x e₁).mpr hF₁.1
  have hm₂ : e₂ ∈ epF x := (mem_epF x e₂).mpr hF₂.1
  by_cases hab : a = b
  · have := ep_signed4 α β L hL hx hB e₁ e₂ e₁ e₁ 1 (-1) 0 0 hm₁ hm₂ hm₁ hm₁ (fun v _ => by
      simp only [H1, H2, hab]; ring) e₁
    rw [if_pos rfl, if_neg (Ne.symm h12)] at this
    norm_num at this
  · have haW : a ∈ epW' α β L x := (mem_epW' _ _ _ _ _).mpr ⟨haL, e₁,
      (mem_epFc _ _ _ _ _).mpr ⟨hF₁.1, (H1 a).mpr (Or.inr rfl)⟩⟩
    have hbW : b ∈ epW' α β L x := (mem_epW' _ _ _ _ _).mpr ⟨hbL, e₂,
      (mem_epFc _ _ _ _ _).mpr ⟨hF₂.1, (H2 b).mpr (Or.inr rfl)⟩⟩
    obtain ⟨e₃, h31, hFa⟩ := ep_card_two_other _ (hdeg a haW) e₁
      ((mem_epFc _ _ _ _ _).mpr ⟨hF₁.1, (H1 a).mpr (Or.inr rfl)⟩)
    obtain ⟨e₄, h42, hFb⟩ := ep_card_two_other _ (hdeg b hbW) e₂
      ((mem_epFc _ _ _ _ _).mpr ⟨hF₂.1, (H2 b).mpr (Or.inr rfl)⟩)
    have hF₃ : (0 < x e₃ ∧ x e₃ < 1) ∧ epCross α β {a} e₃ := by
      rw [← mem_epFc, hFa]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hF₄ : (0 < x e₄ ∧ x e₄ < 1) ∧ epCross α β {b} e₄ := by
      rw [← mem_epFc, hFb]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hm₃ : e₃ ∈ epF x := (mem_epF x e₃).mpr hF₃.1
    have hm₄ : e₄ ∈ epF x := (mem_epF x e₄).mpr hF₄.1
    obtain ⟨hs_c, hp_c⟩ := ep_vertex_two α β L hxQ c hcL e₁ e₂ h12 hFc
    obtain ⟨hs_a, hp_a⟩ := ep_vertex_two α β L hxQ a haL e₁ e₃ (Ne.symm h31) hFa
    obtain ⟨hs_b, hp_b⟩ := ep_vertex_two α β L hxQ b hbL e₂ e₄ (Ne.symm h42) hFb
    have h2a : ¬epCross α β {a} e₂ := by
      rw [H2]; rintro (h | h)
      · exact hac h
      · exact hab h
    have h1b : ¬epCross α β {b} e₁ := by
      rw [H1]; rintro (h | h)
      · exact hbc h
      · exact hab h.symm
    have h32 : e₃ ≠ e₂ := fun h => h2a (h ▸ hF₃.2)
    have h41 : e₄ ≠ e₁ := fun h => h1b (h ▸ hF₄.2)
    obtain ⟨T, hT⟩ : ∃ T : Finset W, T = {a, c, b} := ⟨_, rfl⟩
    have hmemT : ∀ v, v ∈ T ↔ v = a ∨ v = c ∨ v = b := by
      intro v; rw [hT]; simp
    have hTL : T ⊆ L := by
      intro v hv
      rcases (hmemT v).mp hv with h | h | h <;> rw [h] <;> assumption
    have hTcard : T.card = 3 := by
      rw [hT]; exact Finset.card_eq_three.mpr ⟨a, c, b, hac, hab, Ne.symm hbc, rfl⟩
    have hTodd : Odd T.card := by rw [hTcard]; exact ⟨1, rfl⟩
    have hposT : ∀ g, epCross α β T g → 0 < x g → g = e₃ ∨ g = e₄ := by
      intro g hg hgpos
      have hgl := hnl g hgpos
      have : ∃ v u, v ∈ T ∧ u ∉ T ∧ epCross α β {v} g ∧ epCross α β {u} g := by
        unfold epCross at hg
        rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨α g, β g, h1, h2, (ep_cross_ends α β g hgl _).mpr (Or.inl rfl),
            (ep_cross_ends α β g hgl _).mpr (Or.inr rfl)⟩
        · exact ⟨β g, α g, h2, h1, (ep_cross_ends α β g hgl _).mpr (Or.inr rfl),
            (ep_cross_ends α β g hgl _).mpr (Or.inl rfl)⟩
      obtain ⟨v, u, hvT, huT, hv, hu⟩ := this
      have hg1 : g ≠ e₁ := by
        intro h; rw [h] at hu
        rcases (H1 u).mp hu with h' | h'
        · exact huT ((hmemT u).mpr (Or.inr (Or.inl h')))
        · exact huT ((hmemT u).mpr (Or.inl h'))
      have hg2 : g ≠ e₂ := by
        intro h; rw [h] at hu
        rcases (H2 u).mp hu with h' | h'
        · exact huT ((hmemT u).mpr (Or.inr (Or.inl h')))
        · exact huT ((hmemT u).mpr (Or.inr (Or.inr h')))
      rcases (hmemT v).mp hvT with h | h | h
      · rw [h] at hv
        rcases hp_a g hv hgpos with h' | h'
        · exact absurd h' hg1
        · exact Or.inl h'
      · rw [h] at hv
        rcases hp_c g hv hgpos with h' | h'
        · exact absurd h' hg1
        · exact absurd h' hg2
      · rw [h] at hv
        rcases hp_b g hv hgpos with h' | h'
        · exact absurd h' hg2
        · exact Or.inr h'
    by_cases h34 : e₃ = e₄
    · -- a triangle of fractional edges: the cut of `T` carries no weight
      have hnl3 := hnl e₃ hF₃.1.1
      have hin3 : ∀ u, epCross α β {u} e₃ → u ∈ T := by
        intro u hu
        have ea := (ep_cross_ends α β e₃ hnl3 a).mp hF₃.2
        have eb := (ep_cross_ends α β e₃ hnl3 b).mp (h34 ▸ hF₄.2)
        have eu := (ep_cross_ends α β e₃ hnl3 u).mp hu
        have : u = a ∨ u = b := by
          rcases ea with ea | ea <;> rcases eb with eb | eb <;> rcases eu with eu | eu <;>
            first
              | exact absurd (ea.trans eb.symm) hab
              | exact Or.inl (eu.trans ea.symm)
              | exact Or.inr (eu.trans eb.symm)
        rcases this with h | h
        · exact (hmemT u).mpr (Or.inl h)
        · exact (hmemT u).mpr (Or.inr (Or.inr h))
      have hzero : ∑ e ∈ epCut α β T, x e = 0 := by
        refine Finset.sum_eq_zero fun g hg => ?_
        by_contra hne0
        have hgpos := lt_of_le_of_ne (hxQ.1 g) (Ne.symm hne0)
        have hgc := (mem_epCut _ _ _ _).mp hg
        have hge : g = e₃ := by
          rcases hposT g hgc hgpos with h | h
          · exact h
          · exact h.trans h34.symm
        unfold epCross at hgc
        rw [hge] at hgc
        have h1 := hin3 (α e₃) ((ep_cross_ends α β e₃ hnl3 _).mpr (Or.inl rfl))
        have h2 := hin3 (β e₃) ((ep_cross_ends α β e₃ hnl3 _).mpr (Or.inr rfl))
        tauto
      have := hxQ.2.2.2 T hTL hTodd
      rw [hzero] at this
      linarith
    · have hle : ∑ e ∈ epCut α β T, x e ≤ 1 := by
        have h1 : ∑ e ∈ epCut α β T, x e =
            ∑ e ∈ (epCut α β T).filter (fun e => x e ≠ 0), x e :=
          (Finset.sum_filter_ne_zero _).symm
        have hsub : (epCut α β T).filter (fun e => x e ≠ 0) ⊆ {e₃, e₄} := by
          intro g hg
          rw [Finset.mem_filter] at hg
          have := hposT g ((mem_epCut _ _ _ _).mp hg.1)
            (lt_of_le_of_ne (hxQ.1 g) (Ne.symm hg.2))
          rw [Finset.mem_insert, Finset.mem_singleton]; exact this
        have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hxQ.1 i)
        rw [Finset.sum_pair h34] at this
        linarith
      have heven := epQ_even α β L hL hxQ
      have hLcard : 3 ≤ L.card := hTcard ▸ Finset.card_le_card hTL
      by_cases h6 : 6 ≤ L.card
      · have := hB T hTL hTodd (by omega) (by omega)
        linarith
      · have hL4 : L.card = 4 := by
          obtain ⟨k, hk⟩ := heven; omega
        obtain ⟨a', ha'a, ha'end, H3⟩ := ep_other_end α β e₃ (hnl e₃ hF₃.1.1) a hF₃.2
        obtain ⟨b', hb'b, hb'end, H4⟩ := ep_other_end α β e₄ (hnl e₄ hF₄.1.1) b hF₄.2
        have ha'L : a' ∈ L := by
          rcases ha'end with h | h
          · rw [h]; exact (hL e₃).1
          · rw [h]; exact (hL e₃).2
        have hb'L : b' ∈ L := by
          rcases hb'end with h | h
          · rw [h]; exact (hL e₄).1
          · rw [h]; exact (hL e₄).2
        have ha'c : a' ≠ c := by
          intro h
          rcases hp_c e₃ ((H3 c).mpr (Or.inr h.symm)) hF₃.1.1 with h' | h'
          · exact h31 h'
          · exact h32 h'
        have ha'b : a' ≠ b := by
          intro h
          rcases hp_b e₃ ((H3 b).mpr (Or.inr h.symm)) hF₃.1.1 with h' | h'
          · exact h32 h'
          · exact h34 h'
        have hb'c : b' ≠ c := by
          intro h
          rcases hp_c e₄ ((H4 c).mpr (Or.inr h.symm)) hF₄.1.1 with h' | h'
          · exact h41 h'
          · exact h42 h'
        have hb'a : b' ≠ a := by
          intro h
          rcases hp_a e₄ ((H4 a).mpr (Or.inr h.symm)) hF₄.1.1 with h' | h'
          · exact h41 h'
          · exact h34 h'.symm
        have hsd : (L \ T).card = 1 := by
          rw [Finset.card_sdiff_of_subset hTL]; omega
        have ha'm : a' ∈ L \ T := by
          rw [Finset.mem_sdiff, hmemT]
          exact ⟨ha'L, fun h => by rcases h with h | h | h <;> contradiction⟩
        have hb'm : b' ∈ L \ T := by
          rw [Finset.mem_sdiff, hmemT]
          exact ⟨hb'L, fun h => by rcases h with h | h | h <;> contradiction⟩
        have hab' : b' = a' := Finset.card_le_one.mp hsd.le b' hb'm a' ha'm
        rw [hab'] at H4
        have := ep_signed4 α β L hL hx hB e₁ e₂ e₃ e₄ 1 (-1) (-1) 1 hm₁ hm₂ hm₃ hm₄
          (fun v _ => by
            simp only [H1, H2, H3, H4]
            by_cases hvc : v = c <;> by_cases hva : v = a <;> by_cases hvb : v = b <;>
              by_cases hvd : v = a' <;> simp_all) e₁
        rw [if_pos rfl, if_neg (Ne.symm h12), if_neg h31, if_neg h41] at this
        norm_num at this

/-- Case B of Edmonds' theorem: the extreme point is the indicator of a perfect matching. -/
lemma ep_caseB {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (hL : ∀ e, α e ∈ L ∧ β e ∈ L) {x : E → ℝ} (hx : x ∈ (epQ α β L).extremePoints ℝ)
    (hB : epNoTight α β L x) : x ∈ convexHull ℝ (epInd '' epPM α β L) := by
  classical
  have hW := ep_W'_empty α β L hL hx hB
  have hxQ := hx.1
  have h01 : ∀ e, x e = 0 ∨ x e = 1 := by
    intro e
    by_contra hcon
    push Not at hcon
    have hpos : 0 < x e := lt_of_le_of_ne (hxQ.1 e) (Ne.symm hcon.1)
    have hlt : x e < 1 := lt_of_le_of_ne (epQ_le_one α β L hL hxQ e) hcon.2
    have hne : α e ≠ β e := fun h => by rw [hxQ.2.1 e h] at hpos; exact lt_irrefl _ hpos
    have : α e ∈ epW' α β L x := (mem_epW' _ _ _ _ _).mpr ⟨(hL e).1, e,
      (mem_epFc _ _ _ _ _).mpr ⟨⟨hpos, hlt⟩, (ep_cross_ends α β e hne _).mpr (Or.inl rfl)⟩⟩
    rw [hW] at this
    exact absurd this (Finset.notMem_empty _)
  refine subset_convexHull ℝ _ ⟨Finset.univ.filter (fun e => x e = 1), ⟨?_, ?_⟩, ?_⟩
  · intro e he
    rw [Finset.mem_filter] at he
    intro h
    rw [hxQ.2.1 e h] at he
    exact zero_ne_one he.2
  · intro c hc
    have h := hxQ.2.2.1 c hc
    have hsum : ∑ e ∈ epCut α β {c}, x e =
        (((epCut α β {c}).filter (fun e => x e = 1)).card : ℝ) := by
      rw [Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      rcases h01 e with h' | h' <;> simp [h']
    rw [hsum] at h
    have hcard : ((epCut α β {c}).filter (fun e => x e = 1)).card = 1 := by exact_mod_cast h
    obtain ⟨e₀, he₀⟩ := Finset.card_eq_one.mp hcard
    have hmem : ∀ e, (e ∈ Finset.univ.filter (fun e => x e = 1) ∧ epCross α β {c} e) ↔ e = e₀ := by
      intro e
      rw [← Finset.mem_singleton, ← he₀, Finset.mem_filter, Finset.mem_filter, mem_epCut]
      simp only [Finset.mem_univ, true_and]
      tauto
    exact ⟨e₀, (hmem e₀).mpr rfl, fun e he => (hmem e).mp he⟩
  · funext e
    unfold epInd
    rcases h01 e with h' | h'
    · rw [if_neg (by simp [h']), h']
    · rw [if_pos (by simp [h']), h']

/-- **Edmonds' perfect matching polytope theorem**, hard direction: every point satisfying
nonnegativity, the degree constraints and the odd cut constraints is a convex combination of
perfect matchings. -/
theorem ep_main {W E : Type*} [Fintype E] : ∀ (k : ℕ) (α β : E → W) (L : Finset W),
    L.card = k → (∀ e, α e ∈ L ∧ β e ∈ L) →
      epQ α β L ⊆ convexHull ℝ (epInd '' epPM α β L) := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro α β L hk hL
    refine ep_reduce_extreme α β L hL _ fun x hx => ?_
    by_cases hB : epNoTight α β L x
    · exact ep_caseB α β L hL hx hB
    · unfold epNoTight at hB
      push Not at hB
      obtain ⟨T, hTL, hTodd, hT3, hT3', hTle⟩ := hB
      have hxQ := hx.1
      have htight : ∑ e ∈ epCut α β T, x e = 1 := le_antisymm hTle (hxQ.2.2.2 T hTL hTodd)
      have heven := epQ_even α β L hL hxQ
      obtain ⟨t₀, ht₀⟩ : T.Nonempty := Finset.card_pos.mp (by omega)
      have hUcard : (L \ T).card = L.card - T.card := Finset.card_sdiff_of_subset hTL
      obtain ⟨s₀, hs₀⟩ : (L \ T).Nonempty := Finset.card_pos.mp (by omega)
      have hU : ∀ w, w ∈ L \ T ↔ w ∈ L ∧ w ∉ T := fun w => Finset.mem_sdiff
      have hUL : L \ T ⊆ L := Finset.sdiff_subset
      have hUodd : Odd (L \ T).card := by
        rw [hUcard]
        obtain ⟨a, ha⟩ := hTodd
        obtain ⟨b, hb⟩ := heven
        exact ⟨b - a - 1, by omega⟩
      have hUtight : ∑ e ∈ epCut α β (L \ T), x e = 1 := by
        have : epCut α β (L \ T) = epCut α β T := by
          ext e
          rw [mem_epCut, mem_epCut]
          exact epCross_sdiff α β L T (L \ T) hU hL e
        rw [this]; exact htight
      have h1 := ih (epL' L T t₀).card (by rw [epL'_card L T t₀ hTL ht₀]; omega)
        (fun e => epRho T t₀ (α e)) (fun e => epRho T t₀ (β e)) (epL' L T t₀) rfl
        (fun e => ⟨epRho_mem_L' L T t₀ _ (hL e).1, epRho_mem_L' L T t₀ _ (hL e).2⟩)
        (ep_contract_mem α β L T t₀ hTL ht₀ hTodd x hxQ htight)
      have h2 := ih (epL' L (L \ T) s₀).card (by rw [epL'_card L (L \ T) s₀ hUL hs₀]; omega)
        (fun e => epRho (L \ T) s₀ (α e)) (fun e => epRho (L \ T) s₀ (β e)) (epL' L (L \ T) s₀) rfl
        (fun e => ⟨epRho_mem_L' L (L \ T) s₀ _ (hL e).1, epRho_mem_L' L (L \ T) s₀ _ (hL e).2⟩)
        (ep_contract_mem α β L (L \ T) s₀ hUL hs₀ hUodd x hxQ hUtight)
      exact ep_glue α β L T (L \ T) t₀ s₀ hU hL ht₀ hs₀ x hxQ h1 h2

/-- The indicator vector of a perfect matching satisfies all constraints. -/
lemma epInd_mem_epQ {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    {M : Finset E} (hM : M ∈ epPM α β L) : epInd M ∈ epQ α β L := by
  classical
  have hcount : ∀ T : Finset W, ∑ e ∈ epCut α β T, epInd M e =
      ((M.filter (epCross α β T)).card : ℝ) := by
    intro T
    unfold epInd epCut
    rw [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, mul_one]
    congr 2
    ext e
    simp [and_comm]
  have hone : ∀ c ∈ L, (M.filter (epCross α β {c})).card = 1 := by
    intro c hc
    obtain ⟨e₀, ⟨h1, h2⟩, huniq⟩ := hM.2 c hc
    rw [Finset.card_eq_one]
    refine ⟨e₀, ?_⟩
    ext e
    rw [Finset.mem_filter, Finset.mem_singleton]
    exact ⟨fun h => huniq e h, fun h => h ▸ ⟨h1, h2⟩⟩
  refine ⟨fun e => ?_, fun e he => ?_, fun c hc => ?_, fun T hTL hTodd => ?_⟩
  · unfold epInd; split_ifs <;> norm_num
  · unfold epInd; rw [if_neg (fun h => hM.1 e h he)]
  · rw [hcount, hone c hc]; norm_num
  · rw [hcount]
    -- double counting: `|T| = Σ_{e ∈ M} #{c ∈ T : e crosses c}`
    have h1 : ∑ c ∈ T, (M.filter (epCross α β {c})).card = T.card := by
      rw [Finset.sum_congr rfl (fun c hc => hone c (hTL hc))]; simp
    have h2 := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := T) (t := M) (fun c e => epCross α β {c} e)
    have h3 : ∑ c ∈ T, (Finset.bipartiteAbove (fun c e => epCross α β {c} e) M c).card =
        ∑ c ∈ T, (M.filter (epCross α β {c})).card := rfl
    rw [h3, h1] at h2
    -- each edge of `M` not crossing `T` contributes an even number
    have h4 : ∀ e ∈ M, (Finset.bipartiteBelow (fun c e => epCross α β {c} e) T e).card =
        (if epCross α β T e then 1 else 0) + 2 * (if α e ∈ T ∧ β e ∈ T then 1 else 0) := by
      intro e he
      have hne := hM.1 e he
      have hset : Finset.bipartiteBelow (fun c e => epCross α β {c} e) T e =
          T.filter (fun v => v = α e ∨ v = β e) := by
        ext v
        rw [Finset.mem_bipartiteBelow, Finset.mem_filter, ep_cross_ends α β e hne v]
      rw [hset]
      unfold epCross
      by_cases ha : α e ∈ T <;> by_cases hb : β e ∈ T
      · have : T.filter (fun v => v = α e ∨ v = β e) = {α e, β e} := by
          ext v; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · exact fun h => h.2
          · rintro (rfl | rfl)
            · exact ⟨ha, Or.inl rfl⟩
            · exact ⟨hb, Or.inr rfl⟩
        rw [this, Finset.card_pair hne]; simp [ha, hb]
      · have : T.filter (fun v => v = α e ∨ v = β e) = {α e} := by
          ext v; simp only [Finset.mem_filter, Finset.mem_singleton]
          constructor
          · rintro ⟨hv, rfl | rfl⟩
            · rfl
            · exact absurd hv hb
          · rintro rfl; exact ⟨ha, Or.inl rfl⟩
        rw [this]; simp [ha, hb]
      · have : T.filter (fun v => v = α e ∨ v = β e) = {β e} := by
          ext v; simp only [Finset.mem_filter, Finset.mem_singleton]
          constructor
          · rintro ⟨hv, rfl | rfl⟩
            · exact absurd hv ha
            · rfl
          · rintro rfl; exact ⟨hb, Or.inr rfl⟩
        rw [this]; simp [ha, hb]
      · have : T.filter (fun v => v = α e ∨ v = β e) = ∅ := by
          ext v; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
          rintro ⟨hv, rfl | rfl⟩
          · exact ha hv
          · exact hb hv
        rw [this]; simp [ha, hb]
    rw [Finset.sum_congr rfl h4, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.card_filter] at h2
    have hpos : (M.filter (epCross α β T)).card ≠ 0 := by
      intro h0
      rw [h0, zero_add] at h2
      obtain ⟨a, ha⟩ := hTodd
      omega
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hpos

/-- **Edmonds' perfect matching polytope theorem** for a finite multigraph with vertex set `L`,
edge type `E` and end maps `α β : E → W`. -/
theorem ep_edmonds {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (hL : ∀ e, α e ∈ L ∧ β e ∈ L) :
    convexHull ℝ (epInd '' epPM α β L) = epQ α β L := by
  refine Set.Subset.antisymm (convexHull_min ?_ (epQ_convex α β L)) (ep_main L.card α β L rfl hL)
  rintro _ ⟨M, hM, rfl⟩
  exact epInd_mem_epQ α β L hM

/-- Double counting of the incidences between a vertex set `T` and a loop-free edge set `M`. -/
lemma ep_double_count {W E : Type*} [DecidableEq E] (α β : E → W) (M : Finset E)
    (hM : ∀ e ∈ M, α e ≠ β e) (T : Finset W) [DecidablePred (epCross α β T)]
    [∀ c, DecidablePred (epCross α β {c})] [DecidablePred fun e => α e ∈ T ∧ β e ∈ T] :
    ∑ c ∈ T, (M.filter (epCross α β {c})).card =
      (M.filter (epCross α β T)).card + 2 * (M.filter (fun e => α e ∈ T ∧ β e ∈ T)).card := by
  classical
  have h2 := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := T) (t := M) (fun c e => epCross α β {c} e)
  have h3 : ∑ c ∈ T, (Finset.bipartiteAbove (fun c e => epCross α β {c} e) M c).card =
      ∑ c ∈ T, (M.filter (epCross α β {c})).card := by
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
  rw [h3] at h2
  have h4 : ∀ e ∈ M, (Finset.bipartiteBelow (fun c e => epCross α β {c} e) T e).card =
      (if epCross α β T e then 1 else 0) + 2 * (if α e ∈ T ∧ β e ∈ T then 1 else 0) := by
    intro e he
    have hne := hM e he
    have hset : Finset.bipartiteBelow (fun c e => epCross α β {c} e) T e =
        T.filter (fun v => v = α e ∨ v = β e) := by
      ext v
      rw [Finset.mem_bipartiteBelow, Finset.mem_filter, ep_cross_ends α β e hne v]
    rw [hset]
    unfold epCross
    by_cases ha : α e ∈ T <;> by_cases hb : β e ∈ T
    · have : T.filter (fun v => v = α e ∨ v = β e) = {α e, β e} := by
        ext v; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · exact fun h => h.2
        · rintro (rfl | rfl)
          · exact ⟨ha, Or.inl rfl⟩
          · exact ⟨hb, Or.inr rfl⟩
      rw [this, Finset.card_pair hne]; simp [ha, hb]
    · have : T.filter (fun v => v = α e ∨ v = β e) = {α e} := by
        ext v; simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hv, rfl | rfl⟩
          · rfl
          · exact absurd hv hb
        · rintro rfl; exact ⟨ha, Or.inl rfl⟩
      rw [this]; simp [ha, hb]
    · have : T.filter (fun v => v = α e ∨ v = β e) = {β e} := by
        ext v; simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hv, rfl | rfl⟩
          · exact absurd hv ha
          · rfl
        · rintro rfl; exact ⟨hb, Or.inr rfl⟩
      rw [this]; simp [ha, hb]
    · have : T.filter (fun v => v = α e ∨ v = β e) = ∅ := by
        ext v; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
        rintro ⟨hv, rfl | rfl⟩
        · exact ha hv
        · exact hb hv
      rw [this]; simp [ha, hb]
  rw [h2, Finset.sum_congr rfl h4, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.card_filter, ← Finset.card_filter]

/-- In a cubic loop-free multigraph, odd sets have odd cuts. -/
lemma ep_cubic_cut_odd {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (hnl : ∀ e, α e ≠ β e) (hcubic : ∀ c ∈ L, (epCut α β {c}).card = 3) (T : Finset W)
    (hTL : T ⊆ L) (hodd : Odd T.card) : Odd (epCut α β T).card := by
  classical
  have h := ep_double_count α β Finset.univ (fun e _ => hnl e) T
  have h1 : ∑ c ∈ T, (Finset.univ.filter (epCross α β {c})).card = 3 * T.card := by
    have h3 : ∀ c ∈ T, (Finset.univ.filter (epCross α β {c})).card = 3 :=
      fun c hc => hcubic c (hTL hc)
    rw [Finset.sum_congr rfl h3]; simp [mul_comm]
  rw [h1] at h
  unfold epCut
  obtain ⟨a, ha⟩ := hodd
  rw [Nat.odd_iff]
  omega

/-- **Corollary of Edmonds' theorem.** In a cubic loop-free multigraph in which no odd vertex
set has a cut of size one, the vector `(1/3, …, 1/3)` is a convex combination of perfect
matchings, and every edge lies in a perfect matching. -/
theorem ep_cubic_edge_in_pm {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (hL : ∀ e, α e ∈ L ∧ β e ∈ L) (hnl : ∀ e, α e ≠ β e)
    (hcubic : ∀ c ∈ L, (epCut α β {c}).card = 3)
    (hbr : ∀ T ⊆ L, Odd T.card → (epCut α β T).card ≠ 1) :
    (fun _ : E => (1 / 3 : ℝ)) ∈ convexHull ℝ (epInd '' epPM α β L) ∧
      ∀ e : E, ∃ M ∈ epPM α β L, e ∈ M := by
  classical
  have hQ : (fun _ : E => (1 / 3 : ℝ)) ∈ epQ α β L := by
    refine ⟨fun e => by norm_num, fun e he => absurd he (hnl e), fun c hc => ?_,
      fun T hTL hTodd => ?_⟩
    · rw [Finset.sum_const, hcubic c hc]; norm_num
    · rw [Finset.sum_const, nsmul_eq_mul]
      have h1 := ep_cubic_cut_odd α β L hnl hcubic T hTL hTodd
      have h2 := hbr T hTL hTodd
      have h3 : 3 ≤ (epCut α β T).card := by
        obtain ⟨a, ha⟩ := h1; omega
      have : (3 : ℝ) ≤ ((epCut α β T).card : ℝ) := by exact_mod_cast h3
      linarith
  have hhull := ep_main L.card α β L rfl hL hQ
  refine ⟨hhull, fun e => ?_⟩
  obtain ⟨w, hw, hS, -, hx⟩ := ep_hull_repr _ _ hhull
  by_contra hcon
  push Not at hcon
  have := hx e
  rw [Finset.sum_eq_zero] at this
  · norm_num at this
  · intro M _
    by_cases hM : w M = 0
    · rw [hM, zero_mul]
    · have : e ∉ M := hcon M (hS M hM)
      unfold epInd; rw [if_neg this, mul_zero]

/-- First end of an edge of a simple graph. -/
noncomputable def sgα {V : Type*} (G : SimpleGraph V) (e : G.edgeSet) : V := (Quot.out e.1).1

/-- Second end of an edge of a simple graph. -/
noncomputable def sgβ {V : Type*} (G : SimpleGraph V) (e : G.edgeSet) : V := (Quot.out e.1).2

lemma sg_mk {V : Type*} (G : SimpleGraph V) (e : G.edgeSet) : s(sgα G e, sgβ G e) = e.1 :=
  Quot.out_eq e.1

lemma sg_adj {V : Type*} (G : SimpleGraph V) (e : G.edgeSet) : G.Adj (sgα G e) (sgβ G e) := by
  have := e.2
  rw [← sg_mk G e, SimpleGraph.mem_edgeSet] at this
  exact this

lemma sg_cross_iff {V : Type*} (G : SimpleGraph V) (c : V) (e : G.edgeSet) :
    epCross (sgα G) (sgβ G) {c} e ↔ c ∈ e.1 := by
  rw [ep_cross_ends _ _ e (sg_adj G e).ne]
  have := sg_mk G e
  rw [← this, Sym2.mem_iff]

lemma sg_cut_card {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (c : V) : (epCut (sgα G) (sgβ G) {c}).card = G.degree c := by
  classical
  rw [← G.card_incidenceFinset_eq_degree c,
    ← Finset.card_image_of_injective _ Subtype.val_injective]
  congr 1
  ext s
  simp only [Finset.mem_image, mem_epCut, sg_cross_iff, SimpleGraph.mem_incidenceFinset]
  constructor
  · rintro ⟨e, he, rfl⟩; exact ⟨e.2, he⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨s, h1⟩, h2, rfl⟩

lemma sg_bridge {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hbr : G.IsBridgeless) (T : Finset V) :
    (epCut (sgα G) (sgβ G) T).card ≠ 1 := by
  classical
  intro h
  obtain ⟨e₀, he₀⟩ := Finset.card_eq_one.mp h
  have hc : epCross (sgα G) (sgβ G) T e₀ :=
    (mem_epCut _ _ _ _).mp (he₀ ▸ Finset.mem_singleton_self e₀)
  obtain ⟨u, w, hu, hw, huw⟩ : ∃ u w, u ∈ T ∧ w ∉ T ∧ e₀.1 = s(u, w) := by
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨_, _, h1, h2, (sg_mk G e₀).symm⟩
    · exact ⟨_, _, h2, h1, (sg_mk G e₀).symm.trans Sym2.eq_swap⟩
  apply hbr e₀.1 e₀.2
  rw [huw, SimpleGraph.isBridge_iff]
  rintro ⟨p⟩
  have hclosed : ∀ a b, (G.deleteEdges {s(u, w)}).Adj a b → a ∈ T → b ∈ T := by
    intro a b hab ha
    by_contra hb
    rw [SimpleGraph.deleteEdges_adj] at hab
    have hmem : (⟨s(a, b), hab.1⟩ : G.edgeSet) ∈ epCut (sgα G) (sgβ G) T := by
      rw [mem_epCut]
      have hm := sg_mk G ⟨s(a, b), hab.1⟩
      rcases Sym2.eq_iff.mp hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; rw [h1, h2]; exact ⟨ha, hb⟩
      · right; rw [h1, h2]; exact ⟨hb, ha⟩
    rw [he₀, Finset.mem_singleton] at hmem
    apply hab.2
    rw [Set.mem_singleton_iff, ← huw, ← hmem]
  have hwalk : ∀ {a b : V} (q : (G.deleteEdges {s(u, w)}).Walk a b), a ∈ T → b ∈ T := by
    intro a b q
    induction q with
    | nil => exact id
    | cons h _ ih => exact fun ha => ih (hclosed _ _ h ha)
  exact hw (hwalk p hu)

/-- A perfect matching in the multigraph sense gives a perfect matching subgraph. -/
lemma sg_pm_subgraph {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (M : Finset G.edgeSet)
    (hM : M ∈ epPM (sgα G) (sgβ G) Finset.univ) :
    ∃ M' : G.Subgraph, M'.IsPerfectMatching ∧ ∀ e ∈ M, e.1 ∈ M'.edgeSet := by
  classical
  have hle : SimpleGraph.fromEdgeSet (Subtype.val '' (M : Set G.edgeSet)) ≤ G := by
    intro v w h
    rw [SimpleGraph.fromEdgeSet_adj] at h
    obtain ⟨⟨e, -, he⟩, -⟩ := h
    have := e.2
    rw [he, SimpleGraph.mem_edgeSet] at this
    exact this
  have hadj : ∀ v w, (SimpleGraph.toSubgraph _ hle).Adj v w ↔
      s(v, w) ∈ Subtype.val '' (M : Set G.edgeSet) ∧ v ≠ w := fun v w =>
    SimpleGraph.fromEdgeSet_adj _
  refine ⟨SimpleGraph.toSubgraph _ hle, ?_, ?_⟩
  · rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
    intro v
    obtain ⟨e₀, ⟨h1, h2⟩, huniq⟩ := hM.2 v (Finset.mem_univ v)
    rw [sg_cross_iff] at h2
    obtain ⟨w, hw⟩ := h2
    have hvw : G.Adj v w := by
      have := e₀.2; rw [hw, SimpleGraph.mem_edgeSet] at this; exact this
    refine ⟨w, (hadj v w).mpr ⟨⟨e₀, h1, hw⟩, hvw.ne⟩, ?_⟩
    intro w' hw'
    obtain ⟨⟨e, heM, hes⟩, -⟩ := (hadj v w').mp hw'
    have hcr : epCross (sgα G) (sgβ G) {v} e := by
      rw [sg_cross_iff, hes]; exact Sym2.mem_mk_left v w'
    have := huniq e ⟨heM, hcr⟩
    rw [this, hw] at hes
    exact (Sym2.congr_right.mp hes).symm
  · intro e he
    have hm := sg_mk G e
    rw [← hm, SimpleGraph.Subgraph.mem_edgeSet, hadj]
    exact ⟨⟨e, he, hm.symm⟩, (sg_adj G e).ne⟩

/-- **Schönberger / Plesník.** Every edge of a bridgeless cubic simple graph lies in a perfect
matching. In particular (Petersen) such a graph with at least one edge has a perfect matching. -/
theorem sg_cubic_bridgeless_edge_in_pm {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3)
    (hbr : G.IsBridgeless) (e : Sym2 V) (he : e ∈ G.edgeSet) :
    ∃ M : G.Subgraph, M.IsPerfectMatching ∧ e ∈ M.edgeSet := by
  obtain ⟨-, h⟩ := ep_cubic_edge_in_pm (sgα G) (sgβ G) Finset.univ
    (fun _ => ⟨Finset.mem_univ _, Finset.mem_univ _⟩) (fun e => (sg_adj G e).ne)
    (fun c _ => by rw [sg_cut_card, hcubic]) (fun T _ _ => sg_bridge G hbr T)
  obtain ⟨M, hM, heM⟩ := h ⟨e, he⟩
  obtain ⟨M', hM', hsub⟩ := sg_pm_subgraph G M hM
  exact ⟨M', hM', hsub _ heM⟩

/-- A cubic loop-free multigraph on the vertex set `L`. -/
def EpCubic {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) : Prop :=
  (∀ e, α e ∈ L ∧ β e ∈ L) ∧ (∀ e, α e ≠ β e) ∧ ∀ c ∈ L, (epCut α β {c}).card = 3

/-- Bridgeless: no vertex set has a cut consisting of a single edge. -/
def EpBridgeless {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) : Prop :=
  ∀ T ⊆ L, (epCut α β T).card ≠ 1

open Classical in
/-- The set of perfect matchings as a finset. -/
noncomputable def epPMs {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) :
    Finset (Finset E) :=
  Finset.univ.filter (fun M => M ∈ epPM α β L)

/-- The number `m(G)` of perfect matchings. -/
noncomputable def epM {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) : ℕ :=
  (epPMs α β L).card

open Classical in
/-- The number of perfect matchings containing the edge `e`. -/
noncomputable def epMe {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (e : E) : ℕ :=
  ((epPMs α β L).filter (fun M => e ∈ M)).card

lemma mem_epPMs {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (M : Finset E) :
    M ∈ epPMs α β L ↔ M ∈ epPM α β L := by
  classical
  simp [epPMs]

lemma epMe_le_epM {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (e : E) :
    epMe α β L e ≤ epM α β L := by
  classical
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- In a cubic bridgeless multigraph every edge lies in a perfect matching. -/
lemma epMe_pos {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (hc : EpCubic α β L) (hb : EpBridgeless α β L) (e : E) : 0 < epMe α β L e := by
  classical
  obtain ⟨-, h⟩ := ep_cubic_edge_in_pm α β L hc.1 hc.2.1 hc.2.2 (fun T hT _ => hb T hT)
  obtain ⟨M, hM, he⟩ := h e
  exact Finset.card_pos.mpr ⟨M, Finset.mem_filter.mpr ⟨(mem_epPMs _ _ _ _).mpr hM, he⟩⟩

/-- The spanning subgraph of a simple graph with a given set of edges. -/
noncomputable def sgSub {V : Type*} (G : SimpleGraph V) (M : Finset G.edgeSet) : G.Subgraph :=
  SimpleGraph.toSubgraph (SimpleGraph.fromEdgeSet (Subtype.val '' (M : Set G.edgeSet)) ⊓ G)
    inf_le_right

lemma sgSub_adj {V : Type*} (G : SimpleGraph V) (M : Finset G.edgeSet) (v w : V) :
    (sgSub G M).Adj v w ↔ ∃ h : s(v, w) ∈ G.edgeSet, (⟨s(v, w), h⟩ : G.edgeSet) ∈ M := by
  have : (sgSub G M).Adj v w ↔
      (s(v, w) ∈ Subtype.val '' (M : Set G.edgeSet) ∧ v ≠ w) ∧ G.Adj v w := by
    show (SimpleGraph.fromEdgeSet (Subtype.val '' (M : Set G.edgeSet)) ⊓ G).Adj v w ↔ _
    rw [SimpleGraph.inf_adj, SimpleGraph.fromEdgeSet_adj]
  rw [this]
  constructor
  · rintro ⟨⟨⟨e, he, hes⟩, -⟩, hadj⟩
    refine ⟨hadj, ?_⟩
    have : e = ⟨s(v, w), hadj⟩ := Subtype.ext hes
    rw [← this]; exact he
  · rintro ⟨h, hM⟩
    exact ⟨⟨⟨_, hM, rfl⟩, (G.ne_of_adj h)⟩, h⟩

lemma sgSub_isPerfectMatching {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (M : Finset G.edgeSet)
    (hM : M ∈ epPM (sgα G) (sgβ G) Finset.univ) : (sgSub G M).IsPerfectMatching := by
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
  intro v
  obtain ⟨e₀, ⟨h1, h2⟩, huniq⟩ := hM.2 v (Finset.mem_univ v)
  rw [sg_cross_iff] at h2
  obtain ⟨w, hw⟩ := h2
  have hmem : s(v, w) ∈ G.edgeSet := hw ▸ e₀.2
  have he₀ : e₀ = ⟨s(v, w), hmem⟩ := Subtype.ext hw
  refine ⟨w, (sgSub_adj G M v w).mpr ⟨hmem, he₀ ▸ h1⟩, ?_⟩
  intro w' hw'
  obtain ⟨h, hM'⟩ := (sgSub_adj G M v w').mp hw'
  have hcr : epCross (sgα G) (sgβ G) {v} ⟨s(v, w'), h⟩ := by
    rw [sg_cross_iff]; exact Sym2.mem_mk_left v w'
  have := huniq _ ⟨hM', hcr⟩
  rw [he₀] at this
  exact (Sym2.congr_right.mp (congrArg Subtype.val this))

lemma sgSub_injective {V : Type*} (G : SimpleGraph V) : Function.Injective (sgSub G) := by
  intro M N h
  ext e
  obtain ⟨s, hs⟩ := e
  induction s using Sym2.ind with
  | _ v w =>
    have h1 := sgSub_adj G M v w
    have h2 := sgSub_adj G N v w
    rw [h] at h1
    constructor
    · intro he; obtain ⟨_, h'⟩ := h2.mp (h1.mpr ⟨hs, he⟩); exact h'
    · intro he; obtain ⟨_, h'⟩ := h1.mp (h2.mpr ⟨hs, he⟩); exact h'

/-- The multigraph count of perfect matchings bounds the number of perfect matching subgraphs. -/
lemma sg_epM_le {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    epM (sgα G) (sgβ G) Finset.univ ≤ {M : G.Subgraph | M.IsPerfectMatching}.ncard := by
  classical
  unfold epM
  rw [← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard_of_injOn (sgSub G) (fun M hM => ?_)
    ((sgSub_injective G).injOn) (Set.toFinite _)
  exact sgSub_isPerfectMatching G M ((mem_epPMs _ _ _ _).mp (Finset.mem_coe.mp hM))

lemma sg_epCubic {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) :
    EpCubic (sgα G) (sgβ G) Finset.univ :=
  ⟨fun _ => ⟨Finset.mem_univ _, Finset.mem_univ _⟩, fun e => (sg_adj G e).ne,
    fun c _ => by rw [sg_cut_card, hcubic]⟩

lemma sg_epBridgeless {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hbr : G.IsBridgeless) : EpBridgeless (sgα G) (sgβ G) Finset.univ :=
  fun T _ => sg_bridge G hbr T

/-- **Reduction of the target to multigraphs.** An exponential lower bound for all cubic
bridgeless multigraphs (in the `α β L` representation, edge and vertex types in `Type`) gives
the statement for simple graphs. -/
theorem lp_of_multigraph (c : ℝ)
    (H : ∀ (W E : Type) [Fintype E] (α β : E → W) (L : Finset W), EpCubic α β L →
      EpBridgeless α β L → (2 : ℝ) ^ (c * L.card) ≤ epM α β L)
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcubic : ∀ v, G.degree v = 3) (hbr : G.IsBridgeless) :
    (2 : ℝ) ^ (c * Fintype.card V) ≤ ({M : G.Subgraph | M.IsPerfectMatching}.ncard : ℕ) := by
  have h := H V G.edgeSet (sgα G) (sgβ G) Finset.univ (sg_epCubic G hcubic)
    (sg_epBridgeless G hbr)
  rw [Finset.card_univ] at h
  exact h.trans (by exact_mod_cast sg_epM_le G)

/-- Connected: every proper nonempty vertex set has a nonempty cut. -/
def EpConnected {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) : Prop :=
  ∀ T ⊆ L, T.Nonempty → T ≠ L → epCut α β T ≠ ∅

lemma ep_both_in {W E : Type*} [Fintype E] (α β : E → W) (T : Finset W)
    (hT : epCut α β T = ∅) (e : E) : α e ∈ T ↔ β e ∈ T := by
  have : e ∉ epCut α β T := by rw [hT]; exact Finset.notMem_empty e
  rw [mem_epCut] at this
  unfold epCross at this
  tauto

/-- Cuts of the union of components `T` computed inside `T`. -/
lemma ep_restrict_cut {W E : Type*} [Fintype E] (α β : E → W) (T S : Finset W)
    [Fintype {e : E // α e ∈ T}] (hT : epCut α β T = ∅) (hS : S ⊆ T) :
    (epCut (fun e : {e : E // α e ∈ T} => α e.1) (fun e => β e.1) S).card =
      (epCut α β S).card := by
  classical
  refine Finset.card_bij (fun e _ => e.1) (fun e he => ?_) (fun a _ b _ h => Subtype.ext h)
    (fun e he => ?_)
  · rw [mem_epCut] at he ⊢; exact he
  · rw [mem_epCut] at he
    have hα : α e ∈ T := by
      unfold epCross at he
      rcases he with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact hS h1
      · exact (ep_both_in α β T hT e).mpr (hS h2)
    exact ⟨⟨e, hα⟩, (mem_epCut _ _ _ _).mpr he, rfl⟩

lemma ep_restrict_cubic {W E : Type*} [Fintype E] (α β : E → W) (L T : Finset W)
    [Fintype {e : E // α e ∈ T}] (hc : EpCubic α β L) (hTL : T ⊆ L)
    (hT : epCut α β T = ∅) :
    EpCubic (fun e : {e : E // α e ∈ T} => α e.1) (fun e => β e.1) T := by
  refine ⟨fun e => ⟨e.2, (ep_both_in α β T hT e.1).mp e.2⟩, fun e => hc.2.1 e.1, fun c hcT => ?_⟩
  rw [ep_restrict_cut α β T {c} hT (Finset.singleton_subset_iff.mpr hcT)]
  exact hc.2.2 c (hTL hcT)

lemma ep_restrict_bridgeless {W E : Type*} [Fintype E] (α β : E → W) (L T : Finset W)
    [Fintype {e : E // α e ∈ T}] (hb : EpBridgeless α β L) (hTL : T ⊆ L)
    (hT : epCut α β T = ∅) :
    EpBridgeless (fun e : {e : E // α e ∈ T} => α e.1) (fun e => β e.1) T := by
  intro S hS
  rw [ep_restrict_cut α β T S hT hS]
  exact hb S (hS.trans hTL)

/-- Uniqueness in a union of two edge sets living on disjoint vertex sets. -/
lemma ep_split_unique {W E : Type*} [DecidableEq E] (α β : E → W) (A B : Finset E) (c : W)
    (hA : ∃! e, e ∈ A ∧ epCross α β {c} e) (hB : ∀ e ∈ B, ¬epCross α β {c} e) :
    ∃! e, e ∈ A ∪ B ∧ epCross α β {c} e := by
  obtain ⟨e₁, ⟨h1, h2⟩, huniq⟩ := hA
  refine ⟨e₁, ⟨Finset.mem_union_left _ h1, h2⟩, ?_⟩
  rintro e ⟨he, hP⟩
  rcases Finset.mem_union.mp he with h | h
  · exact huniq e ⟨h, hP⟩
  · exact absurd hP (hB e h)

/-- The number of perfect matchings is at least the product over the two sides of an empty
cut. -/
lemma ep_split_count {W E : Type*} [Fintype E] (α β : E → W) (L T T' : Finset W)
    [Fintype {e : E // α e ∈ T}] [Fintype {e : E // α e ∈ T'}]
    (hT' : ∀ w, w ∈ T' ↔ w ∈ L ∧ w ∉ T) (hTL : T ⊆ L) (hL : ∀ e, α e ∈ L ∧ β e ∈ L)
    (hT : epCut α β T = ∅) :
    epM (fun e : {e : E // α e ∈ T} => α e.1) (fun e => β e.1) T *
      epM (fun e : {e : E // α e ∈ T'} => α e.1) (fun e => β e.1) T' ≤ epM α β L := by
  classical
  have hTcut' : epCut α β T' = ∅ := by
    ext e
    rw [mem_epCut, epCross_sdiff α β L T T' hT' hL e, ← mem_epCut, hT]
  unfold epM
  rw [← Finset.card_product]
  refine Finset.card_le_card_of_injOn
    (fun p => p.1.map ⟨Subtype.val, Subtype.val_injective⟩ ∪
      p.2.map ⟨Subtype.val, Subtype.val_injective⟩) ?_ ?_
  · rintro ⟨M₁, M₂⟩ hp
    rw [Finset.mem_coe, Finset.mem_product, mem_epPMs, mem_epPMs] at hp
    obtain ⟨hM₁, hM₂⟩ := hp
    rw [Finset.mem_coe, mem_epPMs]
    dsimp only at hM₁ hM₂ ⊢
    -- transport of the uniqueness statements
    have key : ∀ (S : Finset W) [Fintype {e : E // α e ∈ S}] (M : Finset {e : E // α e ∈ S})
        (c : W), (∃! e, e ∈ M ∧ epCross (fun e : {e : E // α e ∈ S} => α e.1)
          (fun e => β e.1) {c} e) →
        ∃! e, e ∈ M.map ⟨Subtype.val, Subtype.val_injective⟩ ∧ epCross α β {c} e := by
      intro S _ M c h
      obtain ⟨e₁, ⟨h1, h2⟩, huniq⟩ := h
      refine ⟨e₁.1, ⟨Finset.mem_map.mpr ⟨e₁, h1, rfl⟩, h2⟩, ?_⟩
      rintro e ⟨he, hcr⟩
      obtain ⟨e', he', rfl⟩ := Finset.mem_map.mp he
      exact congrArg Subtype.val (huniq e' ⟨he', hcr⟩)
    have notouch : ∀ (S : Finset W) [Fintype {e : E // α e ∈ S}] (M : Finset {e : E // α e ∈ S})
        (c : W), epCut α β S = ∅ → c ∉ S →
        ∀ e ∈ M.map ⟨Subtype.val, Subtype.val_injective⟩, ¬epCross α β {c} e := by
      intro S _ M c hS hc e he hcr
      obtain ⟨e', -, rfl⟩ := Finset.mem_map.mp he
      rw [epCross_singleton] at hcr
      rcases hcr with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact hc (h1 ▸ e'.2)
      · exact hc (h2 ▸ (ep_both_in α β S hS e'.1).mp e'.2)
    refine ⟨fun e he => ?_, fun c hc => ?_⟩
    · rcases Finset.mem_union.mp he with h | h
      · obtain ⟨e', he', rfl⟩ := Finset.mem_map.mp h; exact hM₁.1 e' he'
      · obtain ⟨e', he', rfl⟩ := Finset.mem_map.mp h; exact hM₂.1 e' he'
    · by_cases hcT : c ∈ T
      · exact ep_split_unique α β _ _ c (key T M₁ c (hM₁.2 c hcT))
          (notouch T' M₂ c hTcut' (fun h => ((hT' c).mp h).2 hcT))
      · have hcT' : c ∈ T' := (hT' c).mpr ⟨hc, hcT⟩
        rw [Finset.union_comm]
        exact ep_split_unique α β _ _ c (key T' M₂ c (hM₂.2 c hcT'))
          (notouch T M₁ c hT hcT)
  · rintro ⟨M₁, M₂⟩ - ⟨N₁, N₂⟩ - h
    dsimp only at h
    have hmem : ∀ e : E, (e ∈ M₁.map ⟨Subtype.val, Subtype.val_injective⟩ ∪
        M₂.map ⟨Subtype.val, Subtype.val_injective⟩) ↔
        (e ∈ N₁.map ⟨Subtype.val, Subtype.val_injective⟩ ∪
          N₂.map ⟨Subtype.val, Subtype.val_injective⟩) := fun e => by rw [h]
    have side : ∀ (S S' : Finset W) [Fintype {e : E // α e ∈ S}] [Fintype {e : E // α e ∈ S'}]
        (A : Finset {e : E // α e ∈ S}) (B : Finset {e : E // α e ∈ S'}) (e : {e : E // α e ∈ S}),
        (∀ w, w ∈ S → w ∉ S') →
        (e.1 ∈ A.map ⟨Subtype.val, Subtype.val_injective⟩ ∪
          B.map ⟨Subtype.val, Subtype.val_injective⟩ ↔ e ∈ A) := by
      intro S S' _ _ A B e hdisj
      rw [Finset.mem_union]
      constructor
      · rintro (h | h)
        · obtain ⟨e', he', heq⟩ := Finset.mem_map.mp h
          exact (Subtype.ext heq : e' = e) ▸ he'
        · obtain ⟨e', -, heq⟩ := Finset.mem_map.mp h
          exact absurd e'.2 (hdisj _ (by rw [show α e'.1 = α e.1 from congrArg α heq]; exact e.2))
      · intro h; exact Or.inl (Finset.mem_map.mpr ⟨e, h, rfl⟩)
    have d1 : ∀ w, w ∈ T → w ∉ T' := fun w hw h => ((hT' w).mp h).2 hw
    have d2 : ∀ w, w ∈ T' → w ∉ T := fun w hw => ((hT' w).mp hw).2
    have e1 : M₁ = N₁ := by
      ext e
      rw [← side T T' M₁ M₂ e d1, ← side T T' N₁ N₂ e d1]; exact hmem e.1
    have e2 : M₂ = N₂ := by
      ext e
      have a1 := side T' T M₂ M₁ e d2
      have a2 := side T' T N₂ N₁ e d2
      rw [Finset.union_comm] at a1 a2
      rw [← a1, ← a2]; exact hmem e.1
    rw [e1, e2]

/-- **Reduction to connected multigraphs.** -/
theorem lp_reduce_connected (c : ℝ)
    (H : ∀ (W E : Type) [Fintype E] (α β : E → W) (L : Finset W), EpCubic α β L →
      EpBridgeless α β L → EpConnected α β L → (2 : ℝ) ^ (c * L.card) ≤ epM α β L) :
    ∀ (n : ℕ) (W E : Type) [Fintype E] (α β : E → W) (L : Finset W), L.card = n →
      EpCubic α β L → EpBridgeless α β L → (2 : ℝ) ^ (c * L.card) ≤ epM α β L := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W E _ α β L hn hc hb
    by_cases hconn : EpConnected α β L
    · exact H W E α β L hc hb hconn
    · unfold EpConnected at hconn
      push Not at hconn
      obtain ⟨T, hTL, hTne, hTL', hT⟩ := hconn
      have hT' : ∀ w, w ∈ L \ T ↔ w ∈ L ∧ w ∉ T := fun w => Finset.mem_sdiff
      have hTcut' : epCut α β (L \ T) = ∅ := by
        ext e
        rw [mem_epCut, epCross_sdiff α β L T (L \ T) hT' hc.1 e, ← mem_epCut, hT]
      have hlt : T.card < L.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hTL, hTL'⟩)
      have hpos : 0 < T.card := Finset.card_pos.mpr hTne
      have hsd : (L \ T).card = L.card - T.card := Finset.card_sdiff_of_subset hTL
      have h1 := ih T.card (by omega) W {e : E // α e ∈ T} (fun e => α e.1) (fun e => β e.1) T rfl
        (ep_restrict_cubic α β L T hc hTL hT) (ep_restrict_bridgeless α β L T hb hTL hT)
      have h2 := ih (L \ T).card (by omega) W {e : E // α e ∈ L \ T} (fun e => α e.1)
        (fun e => β e.1) (L \ T) rfl
        (ep_restrict_cubic α β L (L \ T) hc Finset.sdiff_subset hTcut')
        (ep_restrict_bridgeless α β L (L \ T) hb Finset.sdiff_subset hTcut')
      have h3 := ep_split_count α β L T (L \ T) hT' hTL hc.1 hT
      have hcard : (L.card : ℝ) = T.card + (L \ T).card := by
        rw [hsd]; push_cast [Nat.cast_sub hlt.le]; ring
      calc (2 : ℝ) ^ (c * L.card) = 2 ^ (c * T.card) * 2 ^ (c * (L \ T).card) := by
            rw [← Real.rpow_add (by norm_num), hcard]; ring_nf
        _ ≤ (epM (fun e : {e : E // α e ∈ T} => α e.1) (fun e => β e.1) T : ℝ) *
            (epM (fun e : {e : E // α e ∈ L \ T} => α e.1) (fun e => β e.1) (L \ T) : ℝ) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
        _ ≤ epM α β L := by exact_mod_cast h3

/-- Inequality (9) for the rational constants: `2^(2/5) ≤ 4/3`. -/
lemma lp_const9 : (2 : ℝ) ^ ((2 : ℝ) / 5) ≤ 4 / 3 := by
  have h : ((2 : ℝ) ^ ((2 : ℝ) / 5)) ^ (5 : ℕ) ≤ (4 / 3 : ℝ) ^ (5 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) h

/-- Local matchings `M(G, X)`: edge sets inside `E_X` meeting every vertex of `X` exactly once. -/
def epLM {W E : Type*} (α β : E → W) (X : Finset W) : Set (Finset E) :=
  {M | (∀ e ∈ M, α e ∈ X ∨ β e ∈ X) ∧ ∀ c ∈ X, ∃! e, e ∈ M ∧ epCross α β {c} e}

/-- The edge set `D` meets the vertex `c`. -/
def epTouch {W E : Type*} (α β : E → W) (D : Finset E) (c : W) : Prop :=
  ∃ e ∈ D, epCross α β {c} e

lemma ep_unique_iff_card {E : Type*} (A : Finset E) (P : E → Prop) [DecidablePred P] :
    (∃! e, e ∈ A ∧ P e) ↔ (A.filter P).card = 1 := by
  rw [Finset.card_eq_one]
  constructor
  · rintro ⟨e₀, ⟨h1, h2⟩, huniq⟩
    refine ⟨e₀, ?_⟩
    ext e
    rw [Finset.mem_filter, Finset.mem_singleton]
    exact ⟨fun h => huniq e h, fun h => h ▸ ⟨h1, h2⟩⟩
  · rintro ⟨e₀, he₀⟩
    have hmem : ∀ e, (e ∈ A ∧ P e) ↔ e = e₀ := fun e => by
      rw [← Finset.mem_filter, he₀, Finset.mem_singleton]
    exact ⟨e₀, (hmem e₀).mpr rfl, fun e he => (hmem e).mp he⟩

lemma epLM_univ {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (hL : ∀ e, α e ∈ L ∧ β e ∈ L) (hnl : ∀ e, α e ≠ β e) (M : Finset E) :
    M ∈ epLM α β L ↔ M ∈ epPM α β L :=
  ⟨fun h => ⟨fun e _ => hnl e, h.2⟩, fun h => ⟨fun e _ => Or.inl (hL e).1, h.2⟩⟩

/-- Flipping any subfamily of pairwise vertex-disjoint flip sets gives a local matching. -/
theorem ep_flip_union {W E : Type*} [DecidableEq E] (α β : E → W) (X : Finset W)
    {M : Finset E} (hM : M ∈ epLM α β X) {ι : Type*} [DecidableEq ι] (D : ι → Finset E)
    (hin : ∀ i, ∀ e ∈ D i, α e ∈ X ∧ β e ∈ X)
    (hflip : ∀ i, symmDiff M (D i) ∈ epLM α β X)
    (hdisj : ∀ i j, i ≠ j → ∀ c, ¬(epTouch α β (D i) c ∧ epTouch α β (D j) c))
    (S : Finset ι) : symmDiff M (S.biUnion D) ∈ epLM α β X := by
  classical
  have hfs : ∀ (A B : Finset E) (c : W), (symmDiff A B).filter (epCross α β {c}) =
      symmDiff (A.filter (epCross α β {c})) (B.filter (epCross α β {c})) := by
    intro A B c
    ext e
    simp only [Finset.mem_filter, Finset.mem_symmDiff]
    tauto
  refine ⟨fun e he => ?_, fun c hc => ?_⟩
  · rcases Finset.mem_symmDiff.mp he with ⟨h, -⟩ | ⟨h, -⟩
    · exact hM.1 e h
    · obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp h
      exact Or.inl (hin i e hi).1
  · rw [ep_unique_iff_card, hfs]
    by_cases h : ∃ i ∈ S, epTouch α β (D i) c
    · obtain ⟨i₀, hi₀, htouch⟩ := h
      have : (S.biUnion D).filter (epCross α β {c}) = (D i₀).filter (epCross α β {c}) := by
        ext e
        simp only [Finset.mem_filter, Finset.mem_biUnion]
        constructor
        · rintro ⟨⟨j, -, hj⟩, hcr⟩
          by_cases hji : j = i₀
          · exact ⟨hji ▸ hj, hcr⟩
          · exact absurd ⟨⟨e, hj, hcr⟩, htouch⟩ (hdisj j i₀ hji c)
        · rintro ⟨he, hcr⟩; exact ⟨⟨i₀, hi₀, he⟩, hcr⟩
      rw [this, ← hfs, ← ep_unique_iff_card]
      exact (hflip i₀).2 c hc
    · have : (S.biUnion D).filter (epCross α β {c}) = ∅ := by
        ext e
        simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.notMem_empty, iff_false]
        rintro ⟨⟨j, hj, hej⟩, hcr⟩
        exact h ⟨j, hj, e, hej, hcr⟩
      rw [this, ← Finset.bot_eq_empty, symmDiff_bot, ← ep_unique_iff_card]
      exact hM.2 c hc

/-- **Pairwise vertex-disjoint alternating flip sets indexed by `ι` give `2 ^ |ι|` perfect
matchings.** -/
theorem ep_alt_count {W E : Type*} [Fintype E] [DecidableEq E] (α β : E → W) (L : Finset W)
    (hL : ∀ e, α e ∈ L ∧ β e ∈ L) (hnl : ∀ e, α e ≠ β e)
    {M : Finset E} (hM : M ∈ epPM α β L) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ι → Finset E)
    (hne : ∀ i, (D i).Nonempty) (hflip : ∀ i, symmDiff M (D i) ∈ epPM α β L)
    (hdisj : ∀ i j, i ≠ j → ∀ c, ¬(epTouch α β (D i) c ∧ epTouch α β (D j) c)) :
    2 ^ Fintype.card ι ≤ epM α β L := by
  classical
  have hcard : (Finset.univ : Finset (Finset ι)).card = 2 ^ Fintype.card ι := by simp
  rw [← hcard]
  unfold epM
  refine Finset.card_le_card_of_injOn (fun S => symmDiff M (S.biUnion D)) ?_ ?_
  · intro S _
    rw [Finset.mem_coe, mem_epPMs, ← epLM_univ α β L hL hnl]
    exact ep_flip_union α β L ((epLM_univ α β L hL hnl M).mpr hM) D
      (fun i e _ => hL e) (fun i => (epLM_univ α β L hL hnl _).mpr (hflip i)) hdisj S
  · have hsub : ∀ S S' : Finset ι, S.biUnion D = S'.biUnion D → S ⊆ S' := by
      intro S S' h i hi
      obtain ⟨e, he⟩ := hne i
      have : e ∈ S'.biUnion D := h ▸ Finset.mem_biUnion.mpr ⟨i, hi, he⟩
      obtain ⟨j, hj, hej⟩ := Finset.mem_biUnion.mp this
      by_cases hji : j = i
      · exact hji ▸ hj
      · have hcr : epCross α β {α e} e := (ep_cross_ends α β e (hnl e) _).mpr (Or.inl rfl)
        exact absurd ⟨⟨e, hej, hcr⟩, ⟨e, he, hcr⟩⟩ (hdisj j i hji (α e))
    intro S _ S' _ h
    have h' : S.biUnion D = S'.biUnion D := symmDiff_right_injective M h
    exact Finset.Subset.antisymm (hsub S S' h') (hsub S' S h'.symm)

/-- A balanced probability distribution on the local matchings of `X`: every edge of `E_X` has
probability `1/3`. -/
def EpBalanced {W E : Type*} [Fintype E] (α β : E → W) (X : Finset W) (p : Finset E → ℝ) :
    Prop :=
  (∀ N, 0 ≤ p N) ∧ (∀ N, p N ≠ 0 → N ∈ epLM α β X) ∧ ∑ N, p N = 1 ∧
    ∀ e, (α e ∈ X ∨ β e ∈ X) → ∑ N, p N * epInd N e = 1 / 3

open Classical in
/-- `M` admits `k` pairwise vertex-disjoint nonempty flip sets inside `X` ("`k` disjoint
`M`-alternating cycles in `G|X`"). -/
def EpAlt {W E : Type*} (α β : E → W) (X : Finset W) (M : Finset E) (k : ℕ) : Prop :=
  ∃ D : Fin k → Finset E, (∀ i, (D i).Nonempty) ∧ (∀ i, ∀ e ∈ D i, α e ∈ X ∧ β e ∈ X) ∧
    (∀ i, symmDiff M (D i) ∈ epLM α β X) ∧
    ∀ i j, i ≠ j → ∀ c, ¬(epTouch α β (D i) c ∧ epTouch α β (D j) c)

open Classical in
/-- `a(G, X, M)`: the maximum number of disjoint alternating flip sets. -/
noncomputable def epAltNum {W E : Type*} [Fintype E] (α β : E → W) (X : Finset W)
    (M : Finset E) : ℕ :=
  Nat.findGreatest (EpAlt α β X M) (Fintype.card E)

lemma epAltNum_spec {W E : Type*} [Fintype E] (α β : E → W) (X : Finset W) (M : Finset E) :
    EpAlt α β X M (epAltNum α β X M) := by
  classical
  unfold epAltNum
  refine Nat.findGreatest_spec (P := EpAlt α β X M) (Nat.zero_le _) ?_
  exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
    fun i => i.elim0⟩

/-- A burl: every balanced distribution has expected `a(G, X, ·)` at least `1/3`. -/
def EpBurl {W E : Type*} [Fintype E] (α β : E → W) (X : Finset W) : Prop :=
  ∀ p : Finset E → ℝ, EpBalanced α β X p → 1 / 3 ≤ ∑ N, p N * (epAltNum α β X N : ℝ)

/-- The part of a perfect matching inside `E_X` is a local matching. -/
lemma ep_restrict_LM {W E : Type*} [DecidableEq E] (α β : E → W) (L X : Finset W)
    (hXL : X ⊆ L) [DecidablePred fun e => α e ∈ X ∨ β e ∈ X] {M : Finset E}
    (hM : M ∈ epPM α β L) :
    M.filter (fun e => α e ∈ X ∨ β e ∈ X) ∈ epLM α β X := by
  refine ⟨fun e he => (Finset.mem_filter.mp he).2, fun c hc => ?_⟩
  obtain ⟨e₀, ⟨h1, h2⟩, huniq⟩ := hM.2 c (hXL hc)
  have hin : ∀ e, epCross α β {c} e → α e ∈ X ∨ β e ∈ X := by
    intro e he
    rw [epCross_singleton] at he
    rcases he with ⟨h, -⟩ | ⟨-, h⟩
    · exact Or.inl (h ▸ hc)
    · exact Or.inr (h ▸ hc)
  exact ⟨e₀, ⟨Finset.mem_filter.mpr ⟨h1, hin e₀ h2⟩, h2⟩,
    fun e he => huniq e ⟨(Finset.mem_filter.mp he.1).1, he.2⟩⟩

/-- A flip set of the local matching `M ∩ E_X` is a flip set of the perfect matching `M`. -/
lemma ep_flip_global {W E : Type*} [DecidableEq E] (α β : E → W) (L X : Finset W)
    (hnl : ∀ e, α e ≠ β e) [DecidablePred fun e => α e ∈ X ∨ β e ∈ X] {M : Finset E}
    (hM : M ∈ epPM α β L) (D : Finset E) (hD : ∀ e ∈ D, α e ∈ X ∧ β e ∈ X)
    (hflip : symmDiff (M.filter (fun e => α e ∈ X ∨ β e ∈ X)) D ∈ epLM α β X) :
    symmDiff M D ∈ epPM α β L := by
  classical
  refine ⟨fun e _ => hnl e, fun c hc => ?_⟩
  by_cases hcX : c ∈ X
  · obtain ⟨e₀, ⟨h1, h2⟩, huniq⟩ := hflip.2 c hcX
    have hin : ∀ e, epCross α β {c} e → α e ∈ X ∨ β e ∈ X := by
      intro e he
      rw [epCross_singleton] at he
      rcases he with ⟨h, -⟩ | ⟨-, h⟩
      · exact Or.inl (h ▸ hcX)
      · exact Or.inr (h ▸ hcX)
    have hiff : ∀ e, epCross α β {c} e →
        (e ∈ symmDiff (M.filter (fun e => α e ∈ X ∨ β e ∈ X)) D ↔ e ∈ symmDiff M D) := by
      intro e he
      simp only [Finset.mem_symmDiff, Finset.mem_filter, hin e he, and_true]
    exact ⟨e₀, ⟨(hiff e₀ h2).mp h1, h2⟩, fun e he => huniq e ⟨(hiff e he.2).mpr he.1, he.2⟩⟩
  · obtain ⟨e₀, ⟨h1, h2⟩, huniq⟩ := hM.2 c hc
    have hnot : ∀ e ∈ D, ¬epCross α β {c} e := by
      intro e he hcr
      rw [epCross_singleton] at hcr
      rcases hcr with ⟨h, -⟩ | ⟨-, h⟩
      · exact hcX (h ▸ (hD e he).1)
      · exact hcX (h ▸ (hD e he).2)
    refine ⟨e₀, ⟨Finset.mem_symmDiff.mpr (Or.inl ⟨h1, fun h => hnot e₀ h h2⟩), h2⟩, ?_⟩
    rintro e ⟨he, hcr⟩
    rcases Finset.mem_symmDiff.mp he with ⟨h, -⟩ | ⟨h, -⟩
    · exact huniq e ⟨h, hcr⟩
    · exact absurd hcr (hnot e h)

/-- **Corollary 4 (counting form).** A foliage with `k` burls in a cubic bridgeless multigraph
gives at least `2 ^ (k / 3)` perfect matchings. -/
theorem ep_foliage_count {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (hc : EpCubic α β L) (hb : EpBridgeless α β L) {k : ℕ} (X : Fin k → Finset W)
    (hX : ∀ i, X i ⊆ L) (hdisj : ∀ i j, i ≠ j → Disjoint (X i) (X j))
    (hburl : ∀ i, EpBurl α β (X i)) : (2 : ℝ) ^ ((k : ℝ) / 3) ≤ epM α β L := by
  classical
  obtain ⟨hhull, -⟩ := ep_cubic_edge_in_pm α β L hc.1 hc.2.1 hc.2.2 (fun T hT _ => hb T hT)
  obtain ⟨w, hw, hS, hsum, hx⟩ := ep_hull_repr _ _ hhull
  -- the expectation over the restricted distribution
  have hexp : ∀ i, (1 : ℝ) / 3 ≤ ∑ M, w M *
      (epAltNum α β (X i) (M.filter (fun e => α e ∈ X i ∨ β e ∈ X i)) : ℝ) := by
    intro i
    have hpush : ∀ f : Finset E → ℝ,
        ∑ N, (∑ M, if M.filter (fun e => α e ∈ X i ∨ β e ∈ X i) = N then w M else 0) * f N =
          ∑ M, w M * f (M.filter (fun e => α e ∈ X i ∨ β e ∈ X i)) := by
      intro f
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun M _ => ?_
      rw [Finset.sum_eq_single (M.filter (fun e => α e ∈ X i ∨ β e ∈ X i))]
      · rw [if_pos rfl]
      · intro N _ hN; rw [if_neg (Ne.symm hN), zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hbal : EpBalanced α β (X i)
        (fun N => ∑ M, if M.filter (fun e => α e ∈ X i ∨ β e ∈ X i) = N then w M else 0) := by
      refine ⟨fun N => Finset.sum_nonneg fun M _ => by split_ifs; exact hw M; exact le_refl _,
        fun N hN => ?_, ?_, fun e he => ?_⟩
      · obtain ⟨M, -, hM⟩ := Finset.exists_ne_zero_of_sum_ne_zero hN
        have hMN : M.filter (fun e => α e ∈ X i ∨ β e ∈ X i) = N := by
          by_contra h; exact hM (if_neg h)
        rw [if_pos hMN] at hM
        rw [← hMN]
        exact ep_restrict_LM α β L (X i) (hX i) (hS M hM)
      · have := hpush (fun _ => 1)
        simp only [mul_one] at this
        rw [this, hsum]
      · have h3 : (1 : ℝ) / 3 = ∑ M, w M * epInd M e := hx e
        rw [hpush (fun N => epInd N e), h3]
        refine Finset.sum_congr rfl fun M _ => ?_
        congr 1
        unfold epInd
        simp only [Finset.mem_filter, he, and_true]
    have := hburl i _ hbal
    rwa [hpush (fun N => (epAltNum α β (X i) N : ℝ))] at this
  -- some matching in the support has many alternating flip sets
  have htot : (k : ℝ) / 3 ≤ ∑ M, w M *
      ((∑ i, epAltNum α β (X i) (M.filter (fun e => α e ∈ X i ∨ β e ∈ X i)) : ℕ) : ℝ) := by
    have e1 : ∑ M, w M *
        ((∑ i, epAltNum α β (X i) (M.filter (fun e => α e ∈ X i ∨ β e ∈ X i)) : ℕ) : ℝ) =
        ∑ i : Fin k, ∑ M, w M *
          (epAltNum α β (X i) (M.filter (fun e => α e ∈ X i ∨ β e ∈ X i)) : ℝ) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun M _ => ?_
      push_cast
      rw [Finset.mul_sum]
    rw [e1]
    calc (k : ℝ) / 3 = ∑ _i : Fin k, (1 : ℝ) / 3 := by simp; ring
      _ ≤ _ := Finset.sum_le_sum fun i _ => hexp i
  have hA : ∃ M, w M ≠ 0 ∧ (k : ℝ) / 3 ≤
      ((∑ i, epAltNum α β (X i) (M.filter (fun e => α e ∈ X i ∨ β e ∈ X i)) : ℕ) : ℝ) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨M₀, -, hM₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hsum ▸ one_ne_zero)
    have hlt : ∑ M, w M *
        ((∑ i, epAltNum α β (X i) (M.filter (fun e => α e ∈ X i ∨ β e ∈ X i)) : ℕ) : ℝ) <
        ∑ M, w M * ((k : ℝ) / 3) := by
      refine Finset.sum_lt_sum (fun M _ => ?_) ⟨M₀, Finset.mem_univ _, ?_⟩
      · by_cases h : w M = 0
        · rw [h, zero_mul, zero_mul]
        · exact mul_le_mul_of_nonneg_left (hcon M h).le (hw M)
      · exact mul_lt_mul_of_pos_left (hcon M₀ hM₀) (lt_of_le_of_ne (hw M₀) (Ne.symm hM₀))
    rw [← Finset.sum_mul, hsum, one_mul] at hlt
    linarith
  obtain ⟨M, hwM, hk⟩ := hA
  have hMpm := hS M hwM
  have hspec : ∀ i, EpAlt α β (X i) (M.filter (fun e => α e ∈ X i ∨ β e ∈ X i))
      (epAltNum α β (X i) (M.filter (fun e => α e ∈ X i ∨ β e ∈ X i))) :=
    fun i => epAltNum_spec α β (X i) _
  choose D hne hin hflip hdj using hspec
  have hcount := ep_alt_count α β L hc.1 hc.2.1 hMpm
    (fun s : (i : Fin k) × Fin (epAltNum α β (X i)
      (M.filter (fun e => α e ∈ X i ∨ β e ∈ X i))) => D s.1 s.2)
    (fun s => hne s.1 s.2)
    (fun s => ep_flip_global α β L (X s.1) hc.2.1 hMpm _ (hin s.1 s.2) (hflip s.1 s.2))
    (by
      rintro ⟨i, a⟩ ⟨j, b⟩ hneq c ⟨h1, h2⟩
      by_cases hij : i = j
      · subst hij
        exact hdj i a b (fun h => hneq (by rw [h])) c ⟨h1, h2⟩
      · have hmem : ∀ (i : Fin k) (a : Fin (epAltNum α β (X i)
            (M.filter (fun e => α e ∈ X i ∨ β e ∈ X i)))), epTouch α β (D i a) c → c ∈ X i := by
          rintro i a ⟨e, he, hcr⟩
          rw [epCross_singleton] at hcr
          rcases hcr with ⟨h, -⟩ | ⟨-, h⟩
          · exact h ▸ (hin i a e he).1
          · exact h ▸ (hin i a e he).2
        exact Finset.disjoint_left.mp (hdisj i j hij) (hmem i a h1) (hmem j b h2))
  rw [Fintype.card_sigma] at hcount
  simp only [Fintype.card_fin] at hcount
  calc (2 : ℝ) ^ ((k : ℝ) / 3) ≤ (2 : ℝ) ^
        (((∑ i, epAltNum α β (X i) (M.filter (fun e => α e ∈ X i ∨ β e ∈ X i)) : ℕ) : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hk
    _ = ((2 ^ (∑ i, epAltNum α β (X i) (M.filter (fun e => α e ∈ X i ∨ β e ∈ X i))) : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]; push_cast; rfl
    _ ≤ epM α β L := by exact_mod_cast hcount

/-- **Cycles of length two.** Two parallel edges, one in the local matching `M` and one not,
form a flip set: exchanging them gives a local matching again. -/
lemma ep_parallel_flip {W E : Type*} [DecidableEq E] (α β : E → W) (X : Finset W)
    {M : Finset E} (hM : M ∈ epLM α β X) (e f : E) (he : e ∈ M) (hf : f ∉ M)
    (hpar : ∀ v, epCross α β {v} e ↔ epCross α β {v} f) (hinf : α f ∈ X ∧ β f ∈ X) :
    symmDiff M {e, f} ∈ epLM α β X := by
  have hef : e ≠ f := fun h => hf (h ▸ he)
  have hmem : ∀ g, g ∈ symmDiff M ({e, f} : Finset E) ↔ (g ∈ M ∧ g ≠ e) ∨ g = f := by
    intro g
    simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1 | h1, h2⟩)
      · exact Or.inl ⟨h1, fun h => h2 (Or.inl h)⟩
      · exact absurd (h1 ▸ he) h2
      · exact Or.inr h1
    · rintro (⟨h1, h2⟩ | h1)
      · exact Or.inl ⟨h1, fun h => h.elim h2 (fun h' => hf (h' ▸ h1))⟩
      · exact Or.inr ⟨Or.inr h1, h1 ▸ hf⟩
  refine ⟨fun g hg => ?_, fun c hc => ?_⟩
  · rcases (hmem g).mp hg with ⟨h, -⟩ | h
    · exact hM.1 g h
    · exact Or.inl (h ▸ hinf.1)
  · obtain ⟨g₀, ⟨h1, h2⟩, huniq⟩ := hM.2 c hc
    by_cases hg₀ : g₀ = e
    · have hfc : epCross α β {c} f := (hpar c).mp (hg₀ ▸ h2)
      refine ⟨f, ⟨(hmem f).mpr (Or.inr rfl), hfc⟩, ?_⟩
      rintro g ⟨hg, hgc⟩
      rcases (hmem g).mp hg with ⟨h, hne⟩ | h
      · exact absurd ((huniq g ⟨h, hgc⟩).trans hg₀) hne
      · exact h
    · refine ⟨g₀, ⟨(hmem g₀).mpr (Or.inl ⟨h1, hg₀⟩), h2⟩, ?_⟩
      rintro g ⟨hg, hgc⟩
      rcases (hmem g).mp hg with ⟨h, -⟩ | h
      · exact huniq g ⟨h, hgc⟩
      · exfalso
        have hec : epCross α β {c} e := (hpar c).mpr (h ▸ hgc)
        exact hg₀ (huniq e ⟨he, hec⟩).symm

/-- A pair of parallel edges inside `X`, one in `M` and one not, gives `a(G, X, M) ≥ 1`. -/
lemma ep_parallel_altNum {W E : Type*} [Fintype E] (α β : E → W) (X : Finset W)
    {M : Finset E} (hM : M ∈ epLM α β X) (e f : E) (he : e ∈ M) (hf : f ∉ M)
    (hpar : ∀ v, epCross α β {v} e ↔ epCross α β {v} f) (hine : α e ∈ X ∧ β e ∈ X)
    (hinf : α f ∈ X ∧ β f ∈ X) : 1 ≤ epAltNum α β X M := by
  classical
  have halt : EpAlt α β X M 1 := by
    refine ⟨fun _ => {e, f}, fun _ => ⟨e, Finset.mem_insert_self _ _⟩, fun _ g hg => ?_,
      fun _ => ep_parallel_flip α β X hM e f he hf hpar hinf,
      fun i j hij => absurd (Subsingleton.elim i j) hij⟩
    rw [Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl
    · exact hine
    · exact hinf
  unfold epAltNum
  exact Nat.le_findGreatest (Fintype.card_pos_iff.mpr ⟨e⟩) halt

/-- The number of disjoint flip sets is at most `a(G, X, M)`. -/
lemma epAlt_le_altNum {W E : Type*} [Fintype E] (α β : E → W) (X : Finset W)
    (hnl : ∀ e, α e ≠ β e) (M : Finset E) (k : ℕ) (h : EpAlt α β X M k) :
    k ≤ epAltNum α β X M := by
  classical
  have hk : k ≤ Fintype.card E := by
    obtain ⟨D, hne, -, -, hdisj⟩ := h
    choose g hg using hne
    have hinj : Function.Injective g := by
      intro i j hij
      by_contra hne'
      have hcr : epCross α β {α (g i)} (g i) :=
        (ep_cross_ends α β (g i) (hnl _) _).mpr (Or.inl rfl)
      exact hdisj i j hne' (α (g i)) ⟨⟨g i, hg i, hcr⟩, ⟨g i, hij ▸ hg j, hcr⟩⟩
    simpa using Fintype.card_le_of_injective g hinj
  unfold epAltNum
  exact Nat.le_findGreatest hk h

open Classical in
/-- Two distinct local matchings that differ only inside `X` give `a(G, X, M) ≥ 1`. -/
lemma ep_two_LM_altNum {W E : Type*} [Fintype E] (α β : E → W) (X : Finset W)
    (hnl : ∀ e, α e ≠ β e) {M M' : Finset E} (hM' : M' ∈ epLM α β X) (hne : M ≠ M')
    (hin : ∀ e ∈ symmDiff M M', α e ∈ X ∧ β e ∈ X) : 1 ≤ epAltNum α β X M := by
  classical
  refine epAlt_le_altNum α β X hnl M 1 ⟨fun _ => symmDiff M M', fun _ => ?_, fun _ => hin,
    fun _ => ?_, fun i j hij => absurd (Subsingleton.elim i j) hij⟩
  · rw [Finset.nonempty_iff_ne_empty]
    intro h
    exact hne (symmDiff_eq_bot.mp h)
  · show symmDiff M (symmDiff M M') ∈ epLM α β X
    rw [symmDiff_symmDiff_cancel_left]; exact hM'

open Classical in
lemma ep_sum_ind_cut {W E : Type*} [Fintype E] (α β : E → W) (T : Finset W)
    (M : Finset E) :
    ∑ e ∈ epCut α β T, epInd M e = ((M.filter (epCross α β T)).card : ℝ) := by
  classical
  unfold epInd epCut
  rw [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 2
  ext e
  simp [and_comm]

open Classical in
/-- **Claim 3.** If `Y ⊆ X` has a cut of size three, every local matching in the support of a
balanced distribution on `M(G, X)` contains exactly one edge of the cut. -/
lemma ep_claim3 {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (hc : EpCubic α β L)
    (X Y : Finset W) (hXL : X ⊆ L) (hYX : Y ⊆ X) (hY : (epCut α β Y).card = 3)
    (p : Finset E → ℝ) (hp : EpBalanced α β X p) (M : Finset E) (hM : p M ≠ 0) :
    (M.filter (epCross α β Y)).card = 1 := by
  classical
  obtain ⟨hp0, hpS, hp1, hpb⟩ := hp
  -- `|Y|` is odd
  have hYodd : Odd Y.card := by
    have h := ep_double_count α β Finset.univ (fun e _ => hc.2.1 e) Y
    have h3 : ∀ c ∈ Y, (Finset.univ.filter (epCross α β {c})).card = 3 :=
      fun c hcY => hc.2.2 c (hXL (hYX hcY))
    rw [Finset.sum_congr rfl h3, Finset.sum_const, smul_eq_mul] at h
    have hY' : (Finset.univ.filter (epCross α β Y)).card = 3 := hY
    rw [hY'] at h
    rw [Nat.odd_iff]; omega
  -- every local matching meets the cut in an odd number of edges
  have hodd : ∀ N, N ∈ epLM α β X → 1 ≤ (N.filter (epCross α β Y)).card := by
    intro N hN
    have h := ep_double_count α β N (fun e _ => hc.2.1 e) Y
    have h1 : ∀ c ∈ Y, (N.filter (epCross α β {c})).card = 1 :=
      fun c hcY => (ep_unique_iff_card N _).mp (hN.2 c (hYX hcY))
    rw [Finset.sum_congr rfl h1, Finset.sum_const, smul_eq_mul, mul_one] at h
    obtain ⟨a, ha⟩ := hYodd
    omega
  -- the expectation of the number of cut edges is one
  have hexp : ∑ N, p N * ((N.filter (epCross α β Y)).card : ℝ) = 1 := by
    have : ∀ N, p N * ((N.filter (epCross α β Y)).card : ℝ) =
        ∑ e ∈ epCut α β Y, p N * epInd N e := by
      intro N; rw [← Finset.mul_sum, ep_sum_ind_cut]
    rw [Finset.sum_congr rfl (fun N _ => this N), Finset.sum_comm]
    have h3 : ∀ e ∈ epCut α β Y, ∑ N, p N * epInd N e = 1 / 3 := by
      intro e he
      refine hpb e ?_
      rw [mem_epCut] at he
      rcases he with ⟨h, -⟩ | ⟨-, h⟩
      · exact Or.inl (hYX h)
      · exact Or.inr (hYX h)
    rw [Finset.sum_congr rfl h3, Finset.sum_const, hY]; norm_num
  have hzero : ∑ N, p N * (((N.filter (epCross α β Y)).card : ℝ) - 1) = 0 := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hexp, hp1, sub_self]
  have hnn : ∀ N ∈ (Finset.univ : Finset (Finset E)),
      0 ≤ p N * (((N.filter (epCross α β Y)).card : ℝ) - 1) := by
    intro N _
    by_cases hN : p N = 0
    · rw [hN, zero_mul]
    · have : (1 : ℝ) ≤ ((N.filter (epCross α β Y)).card : ℝ) := by
        exact_mod_cast hodd N (hpS N hN)
      exact mul_nonneg (hp0 N) (by linarith)
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hzero M (Finset.mem_univ _)
  have h1 := (mul_eq_zero.mp this).resolve_left hM
  have : ((M.filter (epCross α β Y)).card : ℝ) = 1 := by linarith
  exact_mod_cast this

/-- **Lemma 5(1).** In a cubic bridgeless multigraph, for every edge `e` there are two distinct
perfect matchings avoiding `e`. -/
lemma ep_two_pm_avoiding {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (hc : EpCubic α β L) (hb : EpBridgeless α β L) (e : E) :
    ∃ M₁ M₂, M₁ ∈ epPM α β L ∧ M₂ ∈ epPM α β L ∧ M₁ ≠ M₂ ∧ e ∉ M₁ ∧ e ∉ M₂ := by
  classical
  obtain ⟨-, hpm⟩ := ep_cubic_edge_in_pm α β L hc.1 hc.2.1 hc.2.2 (fun T hT _ => hb T hT)
  have hcard := hc.2.2 (α e) (hc.1 e).1
  have hecut : e ∈ epCut α β {α e} :=
    (mem_epCut _ _ _ _).mpr ((ep_cross_ends α β e (hc.2.1 e) _).mpr (Or.inl rfl))
  have h2 : ((epCut α β {α e}).erase e).card = 2 := by
    rw [Finset.card_erase_of_mem hecut, hcard]
  obtain ⟨f, g, hfg, hfgs⟩ := Finset.card_eq_two.mp h2
  have hf : f ≠ e ∧ epCross α β {α e} f := by
    have : f ∈ (epCut α β {α e}).erase e := by rw [hfgs]; exact Finset.mem_insert_self _ _
    exact ⟨Finset.ne_of_mem_erase this, (mem_epCut _ _ _ _).mp (Finset.mem_of_mem_erase this)⟩
  have hg : g ≠ e ∧ epCross α β {α e} g := by
    have : g ∈ (epCut α β {α e}).erase e := by
      rw [hfgs]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    exact ⟨Finset.ne_of_mem_erase this, (mem_epCut _ _ _ _).mp (Finset.mem_of_mem_erase this)⟩
  obtain ⟨M₁, hM₁, hfM⟩ := hpm f
  obtain ⟨M₂, hM₂, hgM⟩ := hpm g
  have hu₁ := (hM₁.2 (α e) (hc.1 e).1)
  have hu₂ := (hM₂.2 (α e) (hc.1 e).1)
  have hecr : epCross α β {α e} e := (mem_epCut _ _ _ _).mp hecut
  refine ⟨M₁, M₂, hM₁, hM₂, ?_, ?_, ?_⟩
  · intro h
    exact hfg (hu₂.unique ⟨h ▸ hfM, hf.2⟩ ⟨hgM, hg.2⟩)
  · intro h; exact hf.1 (hu₁.unique ⟨hfM, hf.2⟩ ⟨h, hecr⟩)
  · intro h; exact hg.1 (hu₂.unique ⟨hgM, hg.2⟩ ⟨h, hecr⟩)

lemma epCut_contract {W E : Type*} [Fintype E] (α β : E → W) (L T : Finset W) (t₀ : W)
    (ht₀ : t₀ ∈ T) (T' : Finset W) (hT' : T' ⊆ epL' L T t₀) :
    epCut (fun e => epRho T t₀ (α e)) (fun e => epRho T t₀ (β e)) T' =
      epCut α β (epLift T t₀ T') := by
  ext e
  rw [mem_epCut, mem_epCut, epCross_contract α β L T t₀ ht₀ T' hT']

open Classical in
/-- The image of a perfect matching with exactly one edge in `δ(T)` under contraction of `T`. -/
lemma ep_contract_pm {W E : Type*} [Fintype E] (α β : E → W) (L T : Finset W) (t₀ : W)
    (ht₀ : t₀ ∈ T) {M : Finset E} (hM : M ∈ epPM α β L)
    (hone : ∃! f, f ∈ M ∧ epCross α β T f) :
    M.filter (fun e => ¬(α e ∈ T ∧ β e ∈ T)) ∈
      epPM (fun e => epRho T t₀ (α e)) (fun e => epRho T t₀ (β e)) (epL' L T t₀) := by
  refine ⟨fun e he => ?_, fun c hc => ?_⟩
  · rw [Finset.mem_filter] at he
    intro heq
    unfold epRho at heq
    dsimp only at heq
    by_cases ha : α e ∈ T <;> by_cases hb : β e ∈ T
    · exact he.2 ⟨ha, hb⟩
    · rw [if_pos ha, if_neg hb] at heq; exact hb (heq ▸ ht₀)
    · rw [if_neg ha, if_pos hb] at heq; exact ha (heq.symm ▸ ht₀)
    · rw [if_neg ha, if_neg hb] at heq; exact hM.1 e he.1 heq
  · have hsub : ({c} : Finset W) ⊆ epL' L T t₀ := Finset.singleton_subset_iff.mpr hc
    simp only [epCross_contract α β L T t₀ ht₀ {c} hsub]
    have hnin : ∀ S : Finset W, ∀ e, epCross α β S e → S = T ∨ (∀ w ∈ S, w ∉ T) →
        ¬(α e ∈ T ∧ β e ∈ T) := by
      intro S e he hS ⟨h1, h2⟩
      unfold epCross at he
      rcases hS with rfl | hS
      · tauto
      · rcases he with ⟨h, -⟩ | ⟨-, h⟩
        · exact hS _ h h1
        · exact hS _ h h2
    by_cases hct : c = t₀
    · rw [hct, epLift_singleton_t₀ T t₀ ht₀]
      obtain ⟨f, ⟨h1, h2⟩, huniq⟩ := hone
      exact ⟨f, ⟨Finset.mem_filter.mpr ⟨h1, hnin T f h2 (Or.inl rfl)⟩, h2⟩,
        fun g hg => huniq g ⟨(Finset.mem_filter.mp hg.1).1, hg.2⟩⟩
    · rw [epLift_singleton_ne T t₀ c hct]
      unfold epL' at hc
      rw [Finset.mem_insert, Finset.mem_sdiff] at hc
      rcases hc with h | ⟨hcL, hcT⟩
      · exact absurd h hct
      · obtain ⟨f, ⟨h1, h2⟩, huniq⟩ := hM.2 c hcL
        refine ⟨f, ⟨Finset.mem_filter.mpr ⟨h1, hnin {c} f h2 (Or.inr ?_)⟩, h2⟩,
          fun g hg => huniq g ⟨(Finset.mem_filter.mp hg.1).1, hg.2⟩⟩
        intro w hw
        rw [Finset.mem_singleton] at hw
        rw [hw]; exact hcT

open Classical in
/-- **Blossom lifting.** If every edge `f` of `δ(T)` extends to a matching of `T` by edges inside
`T`, then a perfect matching of the contraction `G/T` different from `M/T` lifts to a perfect
matching of `G` different from `M`. -/
lemma ep_blossom_lift {W E : Type*} [Fintype E] (α β : E → W) (L T : Finset W) (t₀ : W)
    (ht₀ : t₀ ∈ T) (M : Finset E)
    (hfc : ∀ f, epCross α β T f → ∃ N : Finset E, (∀ g ∈ N, α g ∈ T ∧ β g ∈ T ∧ α g ≠ β g) ∧
      ∀ c ∈ T, ∃! g, g ∈ insert f N ∧ epCross α β {c} g)
    (M'' : Finset E)
    (hM'' : M'' ∈ epPM (fun e => epRho T t₀ (α e)) (fun e => epRho T t₀ (β e)) (epL' L T t₀))
    (hne : M'' ≠ M.filter (fun e => ¬(α e ∈ T ∧ β e ∈ T))) :
    ∃ M', M' ∈ epPM α β L ∧ M' ≠ M := by
  obtain ⟨f, ⟨hf1, hf2⟩, hfuniq⟩ := epPM_contract_cut α β L T t₀ ht₀ hM''
  obtain ⟨N, hN, hNT⟩ := hfc f hf2
  have hNcross : ∀ g ∈ N, ∀ c, c ∉ T → ¬epCross α β {c} g := by
    intro g hg c hc hcr
    rw [epCross_singleton] at hcr
    rcases hcr with ⟨h, -⟩ | ⟨-, h⟩
    · exact hc (h ▸ (hN g hg).1)
    · exact hc (h ▸ (hN g hg).2.1)
  refine ⟨M'' ∪ N, ⟨fun e he => ?_, fun c hc => ?_⟩, ?_⟩
  · rcases Finset.mem_union.mp he with h | h
    · exact (epPM_contract_noloop α β L T t₀ hM'' h).1
    · exact (hN e h).2.2
  · by_cases hcT : c ∈ T
    · obtain ⟨g₀, ⟨h1, h2⟩, huniq⟩ := hNT c hcT
      have hg₀ : g₀ ∈ M'' ∪ N := by
        rcases Finset.mem_insert.mp h1 with h | h
        · exact Finset.mem_union_left _ (h ▸ hf1)
        · exact Finset.mem_union_right _ h
      refine ⟨g₀, ⟨hg₀, h2⟩, ?_⟩
      rintro g ⟨hg, hgc⟩
      rcases Finset.mem_union.mp hg with h | h
      · have := epPM_contract_touch α β L T t₀ hM'' h c hcT hgc
        have hgf : g = f := hfuniq g ⟨h, this⟩
        exact huniq g ⟨Finset.mem_insert.mpr (Or.inl hgf), hgc⟩
      · exact huniq g ⟨Finset.mem_insert_of_mem h, hgc⟩
    · exact ep_split_unique α β M'' N c (epPM_contract_vertex α β L T t₀ ht₀ hM'' c hc hcT)
        (fun g hg => hNcross g hg c hcT)
  · intro h
    apply hne
    rw [← h]
    ext e
    rw [Finset.mem_filter, Finset.mem_union]
    constructor
    · intro he
      exact ⟨Or.inl he, (epPM_contract_noloop α β L T t₀ hM'' he).2⟩
    · rintro ⟨he | he, hnot⟩
      · exact he
      · exact absurd ⟨(hN e he).1, (hN e he).2.1⟩ hnot

open Classical in
/-- Deleting an edge `f` by turning it into a loop. -/
noncomputable def epDel {W E : Type*} (α β : E → W) (f : E) : E → W :=
  fun e => if e = f then β e else α e

lemma epDel_cross {W E : Type*} (α β : E → W) (f : E) (T : Finset W) (e : E) :
    epCross (epDel α β f) β T e ↔ e ≠ f ∧ epCross α β T e := by
  classical
  unfold epCross epDel
  by_cases h : e = f
  · simp [h]
  · simp [h]

open Classical in
lemma epDel_cut {W E : Type*} [Fintype E] (α β : E → W) (f : E) (T : Finset W) :
    epCut (epDel α β f) β T = (epCut α β T).erase f := by
  ext e
  rw [mem_epCut, Finset.mem_erase, mem_epCut, epDel_cross]

lemma epDel_pm {W E : Type*} (α β : E → W) (f : E) (L : Finset W) {M : Finset E}
    (hM : M ∈ epPM (epDel α β f) β L) : M ∈ epPM α β L := by
  classical
  have hf : ∀ e ∈ M, e ≠ f := by
    intro e he h
    have := hM.1 e he
    unfold epDel at this
    rw [if_pos h] at this
    exact this rfl
  refine ⟨fun e he => ?_, fun c hc => ?_⟩
  · have := hM.1 e he
    unfold epDel at this
    rwa [if_neg (hf e he)] at this
  · obtain ⟨g, ⟨h1, h2⟩, huniq⟩ := hM.2 c hc
    exact ⟨g, ⟨h1, ((epDel_cross α β f {c} g).mp h2).2⟩,
      fun e he => huniq e ⟨he.1, (epDel_cross α β f {c} e).mpr ⟨hf e he.1, he.2⟩⟩⟩

lemma epDel_pm' {W E : Type*} (α β : E → W) (f : E) (L : Finset W) {M : Finset E}
    (hM : M ∈ epPM α β L) (hf : f ∉ M) : M ∈ epPM (epDel α β f) β L := by
  classical
  have hne : ∀ e ∈ M, e ≠ f := fun e he h => hf (h ▸ he)
  refine ⟨fun e he => ?_, fun c hc => ?_⟩
  · unfold epDel; rw [if_neg (hne e he)]; exact hM.1 e he
  · obtain ⟨g, ⟨h1, h2⟩, huniq⟩ := hM.2 c hc
    exact ⟨g, ⟨h1, (epDel_cross α β f {c} g).mpr ⟨hne g h1, h2⟩⟩,
      fun e he => huniq e ⟨he.1, ((epDel_cross α β f {c} e).mp he.2).2⟩⟩

open Classical in
/-- The part of a glued matching outside `T` is the first matching. -/
lemma ep_glue_filter {W E : Type*} [Fintype E] (α β : E → W) (L T U : Finset W) (t₀ s₀ : W)
    (hL : ∀ e, α e ∈ L ∧ β e ∈ L) (hU : ∀ w, w ∈ U ↔ w ∈ L ∧ w ∉ T) (hs₀ : s₀ ∈ U)
    {N₁ N₂ : Finset E}
    (hN₁ : N₁ ∈ epPM (fun e => epRho T t₀ (α e)) (fun e => epRho T t₀ (β e)) (epL' L T t₀))
    (hN₂ : N₂ ∈ epPM (fun e => epRho U s₀ (α e)) (fun e => epRho U s₀ (β e)) (epL' L U s₀))
    (g : E) (hg₁ : g ∈ N₁) (hg₂ : g ∈ N₂) (hgc : epCross α β T g) :
    (N₁ ∪ N₂).filter (fun e => ¬(α e ∈ T ∧ β e ∈ T)) = N₁ := by
  have hcut₂ := epPM_contract_cut α β L U s₀ hs₀ hN₂
  simp only [epCross_sdiff α β L T U hU hL] at hcut₂
  ext e
  rw [Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨he | he, hnot⟩
    · exact he
    · have hn := (epPM_contract_noloop α β L U s₀ hN₂ he).2
      simp only [hU, (hL e).1, (hL e).2, true_and] at hn
      have hc : epCross α β T e := by unfold epCross; tauto
      exact (hcut₂.unique ⟨he, hc⟩ ⟨hg₂, hgc⟩) ▸ hg₁
  · intro he
    exact ⟨Or.inl he, (epPM_contract_noloop α β L T t₀ hN₁ he).2⟩

lemma ep_cross_of_ends {W E : Type*} (α β : E → W) (e : E) (hne : α e ≠ β e) (v u : W)
    (hv : epCross α β {v} e) (hu : epCross α β {u} e) (hvu : v ≠ u) (T : Finset W)
    (hvT : v ∈ T) (huT : u ∉ T) : epCross α β T e := by
  have h1 := (ep_cross_ends α β e hne v).mp hv
  have h2 := (ep_cross_ends α β e hne u).mp hu
  unfold epCross
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hvu
  · left; exact ⟨h1 ▸ hvT, h2 ▸ huT⟩
  · right; exact ⟨h2 ▸ huT, h1 ▸ hvT⟩
  · exact absurd (h1.trans h2.symm) hvu

lemma ep_ends_of_cross {W E : Type*} (α β : E → W) (e : E) (T : Finset W)
    (hc : epCross α β T e) :
    ∃ v u, v ∈ T ∧ u ∉ T ∧ ∀ c, epCross α β {c} e ↔ c = v ∨ c = u := by
  unfold epCross at hc
  rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hne : α e ≠ β e := fun h => h2 (h ▸ h1)
    exact ⟨α e, β e, h1, h2, fun c => ep_cross_ends α β e hne c⟩
  · have hne : α e ≠ β e := fun h => h1 (h ▸ h2)
    exact ⟨β e, α e, h2, h1, fun c => by rw [ep_cross_ends α β e hne c]; tauto⟩

lemma ep_exu2 {E : Type*} [DecidableEq E] (a b : E) (P : E → Prop) (ha : P a) (hb : ¬P b) :
    (∃! g, g ∈ insert a ({b} : Finset E) ∧ P g) ∧ (∃! g, g ∈ insert b ({a} : Finset E) ∧ P g) := by
  constructor
  · refine ⟨a, ⟨Finset.mem_insert_self _ _, ha⟩, ?_⟩
    rintro g ⟨hg, hP⟩
    rcases Finset.mem_insert.mp hg with h | h
    · exact h
    · exact absurd ((Finset.mem_singleton.mp h) ▸ hP) hb
  · refine ⟨a, ⟨Finset.mem_insert_of_mem (Finset.mem_singleton_self _), ha⟩, ?_⟩
    rintro g ⟨hg, hP⟩
    rcases Finset.mem_insert.mp hg with h | h
    · exact absurd (h ▸ hP) hb
    · exact Finset.mem_singleton.mp h

open Classical in
/-- **Kotzig's theorem** (multigraph form): a nonempty perfect matching none of whose edges is a
bridge is not the only perfect matching. -/
theorem ep_kotzig {W E : Type*} [Fintype E] : ∀ (n : ℕ) (α β : E → W) (L : Finset W),
    L.card + (Finset.univ.filter (fun e => α e ≠ β e)).card = n →
    (∀ e, α e ∈ L ∧ β e ∈ L) → ∀ M : Finset E, M ∈ epPM α β L → M.Nonempty →
    (∀ e ∈ M, ∀ T ⊆ L, epCut α β T ≠ {e}) → ∃ M', M' ∈ epPM α β L ∧ M' ≠ M := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro α β L hn hL M hM hMne hbr
    -- parity of sets with exactly one matching edge in the cut
    have hpar : ∀ T ⊆ L, (M.filter (epCross α β T)).card = 1 → Odd T.card := by
      intro T hT h1
      have h := ep_double_count α β M hM.1 T
      have h2 : ∀ c ∈ T, (M.filter (epCross α β {c})).card = 1 :=
        fun c hc => (ep_unique_iff_card M _).mp (hM.2 c (hT hc))
      rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, mul_one, h1] at h
      rw [Nat.odd_iff]; omega
    have hLeven : Even L.card := by
      have h := ep_double_count α β M hM.1 L
      have h2 : ∀ c ∈ L, (M.filter (epCross α β {c})).card = 1 :=
        fun c hc => (ep_unique_iff_card M _).mp (hM.2 c hc)
      have h0 : M.filter (epCross α β L) = ∅ := by
        ext e
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
        rintro ⟨-, hc⟩
        unfold epCross at hc
        have := hL e; tauto
      rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, mul_one, h0,
        Finset.card_empty] at h
      rw [Nat.even_iff]; omega
    -- contraction of an odd set with one matching edge in its cut: induction applies
    have key : ∀ (T : Finset W) (t₀ : W), T ⊆ L → t₀ ∈ T → 3 ≤ T.card →
        (∃! g, g ∈ M ∧ epCross α β T g) →
        ∃ M'', M'' ∈ epPM (fun e => epRho T t₀ (α e)) (fun e => epRho T t₀ (β e))
          (epL' L T t₀) ∧ M'' ≠ M.filter (fun e => ¬(α e ∈ T ∧ β e ∈ T)) := by
      intro T t₀ hTL ht₀ hT3 hone
      have hM₁ := ep_contract_pm α β L T t₀ ht₀ hM hone
      have hcard := epL'_card L T t₀ hTL ht₀
      have hle := Finset.card_le_card hTL
      have hnl : (Finset.univ.filter
          (fun e => epRho T t₀ (α e) ≠ epRho T t₀ (β e))).card ≤
          (Finset.univ.filter (fun e => α e ≠ β e)).card := by
        refine Finset.card_le_card fun e he => ?_
        rw [Finset.mem_filter] at he ⊢
        exact ⟨he.1, fun h => he.2 (by rw [h])⟩
      refine ih _ (by omega) (fun e => epRho T t₀ (α e)) (fun e => epRho T t₀ (β e))
        (epL' L T t₀) rfl
        (fun e => ⟨epRho_mem_L' L T t₀ _ (hL e).1, epRho_mem_L' L T t₀ _ (hL e).2⟩)
        _ hM₁ ?_ ?_
      · obtain ⟨g, ⟨hg1, hg2⟩, -⟩ := hone
        refine ⟨g, Finset.mem_filter.mpr ⟨hg1, ?_⟩⟩
        unfold epCross at hg2; tauto
      · intro e he T' hT'
        rw [epCut_contract α β L T t₀ ht₀ T' hT']
        exact hbr e (Finset.mem_filter.mp he).1 _ (epLift_subset L T t₀ hTL ht₀ T' hT')
    obtain ⟨e₀, he₀⟩ := hMne
    have hx : α e₀ ∈ L := (hL e₀).1
    have he₀c : epCross α β {α e₀} e₀ :=
      (ep_cross_ends α β e₀ (hM.1 e₀ he₀) _).mpr (Or.inl rfl)
    -- another edge at `α e₀`
    obtain ⟨f, hfc, hfe⟩ : ∃ f, epCross α β {α e₀} f ∧ f ≠ e₀ := by
      by_contra hcon
      push Not at hcon
      apply hbr e₀ he₀ {α e₀} (Finset.singleton_subset_iff.mpr hx)
      rw [Finset.eq_singleton_iff_unique_mem]
      exact ⟨(mem_epCut _ _ _ _).mpr he₀c, fun g hg => hcon g ((mem_epCut _ _ _ _).mp hg)⟩
    have hfM : f ∉ M := fun h => hfe ((hM.2 _ hx).unique ⟨h, hfc⟩ ⟨he₀, he₀c⟩)
    have hfnl : α f ≠ β f := by
      intro h; unfold epCross at hfc; rw [h] at hfc; tauto
    by_cases hcase : ∀ e ∈ M, ∀ T ⊆ L, epCut (epDel α β f) β T ≠ {e}
    · -- delete `f`
      have hmeas : (Finset.univ.filter (fun e => epDel α β f e ≠ β e)).card <
          (Finset.univ.filter (fun e => α e ≠ β e)).card := by
        refine Finset.card_lt_card (Finset.ssubset_iff_of_subset (fun e he => ?_) |>.mpr
          ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfnl⟩, ?_⟩)
        · rw [Finset.mem_filter] at he ⊢
          refine ⟨he.1, fun h => he.2 ?_⟩
          unfold epDel; split_ifs
          · rfl
          · exact h
        · rw [Finset.mem_filter]; rintro ⟨-, h⟩
          unfold epDel at h; rw [if_pos rfl] at h; exact h rfl
      obtain ⟨M', hM', hne⟩ := ih _ (by omega) (epDel α β f) β L rfl
        (fun e => ⟨by unfold epDel; split_ifs; exact (hL e).2; exact (hL e).1, (hL e).2⟩)
        M (epDel_pm' α β f L hM hfM) ⟨e₀, he₀⟩ hcase
      exact ⟨M', epDel_pm α β f L hM', hne⟩
    · push Not at hcase
      obtain ⟨b, hbM, A, hAL, hA⟩ := hcase
      rw [epDel_cut] at hA
      have hbf : b ≠ f := fun h => hfM (h ▸ hbM)
      have hfA : f ∈ epCut α β A := by
        by_contra hf
        exact hbr b hbM A hAL (by rw [← hA, Finset.erase_eq_of_notMem hf])
      have hcutA : ∀ g, epCross α β A g ↔ g = b ∨ g = f := by
        intro g
        rw [← mem_epCut]
        by_cases hg : g = f
        · rw [hg]; exact ⟨fun _ => Or.inr rfl, fun _ => hfA⟩
        · have : g ∈ (epCut α β A).erase f ↔ g = b := by rw [hA, Finset.mem_singleton]
          rw [Finset.mem_erase] at this
          constructor
          · intro h; exact Or.inl (this.mp ⟨hg, h⟩)
          · rintro (h | h)
            · exact (this.mpr h).2
            · exact absurd h hg
      have hbA : epCross α β A b := (hcutA b).mpr (Or.inl rfl)
      have honeA : ∃! g, g ∈ M ∧ epCross α β A g :=
        ⟨b, ⟨hbM, hbA⟩, fun g hg => ((hcutA g).mp hg.2).resolve_right (fun h => hfM (h ▸ hg.1))⟩
      have hAodd : Odd A.card := hpar A hAL ((ep_unique_iff_card M _).mp honeA)
      have hU : ∀ w, w ∈ L \ A ↔ w ∈ L ∧ w ∉ A := fun w => Finset.mem_sdiff
      have hAU : ∀ w, w ∈ A ↔ w ∈ L ∧ w ∉ L \ A := by
        intro w; rw [Finset.mem_sdiff]
        constructor
        · intro h; exact ⟨hAL h, fun h' => h'.2 h⟩
        · rintro ⟨h1, h2⟩; by_contra h; exact h2 ⟨h1, h⟩
      have hcutU : ∀ g, epCross α β (L \ A) g ↔ g = b ∨ g = f := fun g => by
        rw [epCross_sdiff α β L A (L \ A) hU hL, hcutA]
      have honeU : ∃! g, g ∈ M ∧ epCross α β (L \ A) g :=
        ⟨b, ⟨hbM, (hcutU b).mpr (Or.inl rfl)⟩,
          fun g hg => ((hcutU g).mp hg.2).resolve_right (fun h => hfM (h ▸ hg.1))⟩
      have hUcard : (L \ A).card = L.card - A.card := Finset.card_sdiff_of_subset hAL
      have hAle := Finset.card_le_card hAL
      have hUodd : Odd (L \ A).card := by
        rw [hUcard]
        obtain ⟨a, ha⟩ := hAodd
        obtain ⟨c, hc⟩ := hLeven
        exact ⟨c - a - 1, by omega⟩
      by_cases hbig : 3 ≤ A.card ∧ 3 ≤ (L \ A).card
      · -- both sides are large: contract each side and glue
        obtain ⟨t₀, ht₀⟩ : A.Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨s₀, hs₀⟩ : (L \ A).Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨N₁, hN₁, hne₁⟩ := key A t₀ hAL ht₀ hbig.1 honeA
        obtain ⟨N₂, hN₂, hne₂⟩ := key (L \ A) s₀ Finset.sdiff_subset hs₀ hbig.2 honeU
        have hM₁ := ep_contract_pm α β L A t₀ ht₀ hM honeA
        have hM₂ := ep_contract_pm α β L (L \ A) s₀ hs₀ hM honeU
        obtain ⟨g₁, ⟨hg₁, hg₁c⟩, -⟩ := epPM_contract_cut α β L A t₀ ht₀ hN₁
        obtain ⟨g₂, ⟨hg₂, hg₂c⟩, -⟩ := epPM_contract_cut α β L (L \ A) s₀ hs₀ hN₂
        have hb₁ : b ∈ M.filter (fun e => ¬(α e ∈ A ∧ β e ∈ A)) :=
          Finset.mem_filter.mpr ⟨hbM, by unfold epCross at hbA; tauto⟩
        have hbU := (hcutU b).mpr (Or.inl rfl)
        have hb₂ : b ∈ M.filter (fun e => ¬(α e ∈ L \ A ∧ β e ∈ L \ A)) :=
          Finset.mem_filter.mpr ⟨hbM, by unfold epCross at hbU; tauto⟩
        rcases (hcutA g₁).mp hg₁c with h1 | h1
        · -- `N₁` uses `b`: glue with `M/U`
          refine ⟨N₁ ∪ M.filter (fun e => ¬(α e ∈ L \ A ∧ β e ∈ L \ A)),
            ep_glue_mem α β L A (L \ A) t₀ s₀ hL ht₀ hU hs₀ hN₁ hM₂ b (h1 ▸ hg₁) hb₂ hbA, ?_⟩
          intro h
          apply hne₁
          rw [← ep_glue_filter α β L A (L \ A) t₀ s₀ hL hU hs₀ hN₁ hM₂ b (h1 ▸ hg₁) hb₂ hbA, h]
        · rcases (hcutU g₂).mp hg₂c with h2 | h2
          · -- `N₂` uses `b`: glue with `M/A`
            have hmem := ep_glue_mem α β L A (L \ A) t₀ s₀ hL ht₀ hU hs₀ hM₁ hN₂ b hb₁
              (h2 ▸ hg₂) hbA
            refine ⟨M.filter (fun e => ¬(α e ∈ A ∧ β e ∈ A)) ∪ N₂, hmem, ?_⟩
            intro h
            apply hne₂
            have := ep_glue_filter α β L (L \ A) A s₀ t₀ hL hAU ht₀ hN₂ hM₁ b (h2 ▸ hg₂) hb₁ hbU
            rw [← this, Finset.union_comm, h]
          · -- both use `f`
            refine ⟨N₁ ∪ N₂, ep_glue_mem α β L A (L \ A) t₀ s₀ hL ht₀ hU hs₀ hN₁ hN₂ f
              (h1 ▸ hg₁) (h2 ▸ hg₂) ((hcutA f).mpr (Or.inr rfl)), ?_⟩
            intro h
            exact hfM (h ▸ Finset.mem_union_left _ (h1 ▸ hg₁))
      · -- one side is a single vertex `p` of degree two
        obtain ⟨p, hpL, hcutp⟩ : ∃ p, p ∈ L ∧ ∀ g, epCross α β {p} g ↔ g = b ∨ g = f := by
          by_cases hA3 : 3 ≤ A.card
          · have h1 : (L \ A).card = 1 := by
              obtain ⟨a, ha⟩ := hUodd
              have : ¬3 ≤ (L \ A).card := fun h => hbig ⟨hA3, h⟩
              omega
            obtain ⟨p, hp⟩ := Finset.card_eq_one.mp h1
            refine ⟨p, ?_, fun g => by rw [← hp]; exact hcutU g⟩
            have : p ∈ L \ A := by rw [hp]; exact Finset.mem_singleton_self p
            exact (Finset.mem_sdiff.mp this).1
          · have h1 : A.card = 1 := by
              obtain ⟨a, ha⟩ := hAodd; omega
            obtain ⟨p, hp⟩ := Finset.card_eq_one.mp h1
            exact ⟨p, hAL (by rw [hp]; exact Finset.mem_singleton_self p),
              fun g => by rw [← hp]; exact hcutA g⟩
        have hbp := (hcutp b).mpr (Or.inl rfl)
        have hfp := (hcutp f).mpr (Or.inr rfl)
        obtain ⟨q, hqp, hqend, Hb⟩ := ep_other_end α β b (hM.1 b hbM) p hbp
        obtain ⟨r, hrp, hrend, Hf⟩ := ep_other_end α β f hfnl p hfp
        have hqL : q ∈ L := by
          rcases hqend with h | h
          · rw [h]; exact (hL b).1
          · rw [h]; exact (hL b).2
        have hrL : r ∈ L := by
          rcases hrend with h | h
          · rw [h]; exact (hL f).1
          · rw [h]; exact (hL f).2
        by_cases hqr : q = r
        · -- `b` and `f` are parallel
          have hpar' : ∀ v, epCross α β {v} b ↔ epCross α β {v} f := fun v => by
            rw [Hb, Hf, hqr]
          have hLM : M ∈ epLM α β L := ⟨fun e _ => Or.inl (hL e).1, hM.2⟩
          have hflip := ep_parallel_flip α β L hLM b f hbM hfM hpar' (hL f)
          refine ⟨symmDiff M {b, f}, ⟨fun e he => ?_, hflip.2⟩, ?_⟩
          · rcases Finset.mem_symmDiff.mp he with ⟨h, -⟩ | ⟨h, -⟩
            · exact hM.1 e h
            · rcases Finset.mem_insert.mp h with h | h
              · rw [h]; exact hM.1 b hbM
              · rw [Finset.mem_singleton.mp h]; exact hfnl
          · intro h
            apply hfM
            rw [← h]
            exact Finset.mem_symmDiff.mpr (Or.inr
              ⟨Finset.mem_insert_of_mem (Finset.mem_singleton_self f), hfM⟩)
        · -- the triple `{q, p, r}` is a blossom
          obtain ⟨T, hT⟩ : ∃ T : Finset W, T = {q, p, r} := ⟨_, rfl⟩
          have hmemT : ∀ v, v ∈ T ↔ v = q ∨ v = p ∨ v = r := by
            intro v; rw [hT]; simp
          have hTL : T ⊆ L := by
            intro v hv
            rcases (hmemT v).mp hv with h | h | h <;> rw [h] <;> assumption
          have hTcard : T.card = 3 := by
            rw [hT]; exact Finset.card_eq_three.mpr ⟨q, p, r, hqp, hqr, Ne.symm hrp, rfl⟩
          have hpT : p ∈ T := (hmemT p).mpr (Or.inr (Or.inl rfl))
          have hbq : epCross α β {q} b := (Hb q).mpr (Or.inr rfl)
          have hfr : epCross α β {r} f := (Hf r).mpr (Or.inr rfl)
          have hbr' : ¬epCross α β {r} b := by
            rw [Hb]; rintro (h | h)
            · exact hrp h
            · exact hqr h.symm
          have hfq : ¬epCross α β {q} f := by
            rw [Hf]; rintro (h | h)
            · exact hqp h
            · exact hqr h
          obtain ⟨gr, ⟨hgrM, hgrc⟩, hgru⟩ := hM.2 r hrL
          have hgrb : gr ≠ b := fun h => hbr' (h ▸ hgrc)
          have hgrf : gr ≠ f := fun h => hfM (h ▸ hgrM)
          obtain ⟨r', hr'r, -, Hg⟩ := ep_other_end α β gr (hM.1 gr hgrM) r hgrc
          have hr'T : r' ∉ T := by
            intro h
            have hcr : epCross α β {r'} gr := (Hg r').mpr (Or.inr rfl)
            rcases (hmemT r').mp h with h | h | h
            · rw [h] at hcr
              exact hgrb ((hM.2 q hqL).unique ⟨hgrM, hcr⟩ ⟨hbM, hbq⟩)
            · rw [h] at hcr
              rcases (hcutp gr).mp hcr with h' | h'
              · exact hgrb h'
              · exact hgrf h'
            · exact hr'r h
          have hgrT : epCross α β T gr :=
            ep_cross_of_ends α β gr (hM.1 gr hgrM) r r' hgrc ((Hg r').mpr (Or.inr rfl))
              (Ne.symm hr'r) T ((hmemT r).mpr (Or.inr (Or.inr rfl))) hr'T
          have hbT : ¬epCross α β T b := by
            intro h
            obtain ⟨v, u, -, huT, H⟩ := ep_ends_of_cross α β b T h
            have := (Hb u).mp ((H u).mpr (Or.inr rfl))
            rcases this with h' | h'
            · exact huT (h' ▸ hpT)
            · exact huT ((hmemT u).mpr (Or.inl h'))
          have hfT : ¬epCross α β T f := by
            intro h
            obtain ⟨v, u, -, huT, H⟩ := ep_ends_of_cross α β f T h
            have := (Hf u).mp ((H u).mpr (Or.inr rfl))
            rcases this with h' | h'
            · exact huT (h' ▸ hpT)
            · exact huT ((hmemT u).mpr (Or.inr (Or.inr h')))
          have honeT : ∃! g, g ∈ M ∧ epCross α β T g := by
            refine ⟨gr, ⟨hgrM, hgrT⟩, ?_⟩
            rintro g ⟨hgM, hgT⟩
            obtain ⟨v, u, hvT, -, H⟩ := ep_ends_of_cross α β g T hgT
            have hgv : epCross α β {v} g := (H v).mpr (Or.inl rfl)
            rcases (hmemT v).mp hvT with h | h | h
            · rw [h] at hgv
              exact absurd ((hM.2 q hqL).unique ⟨hgM, hgv⟩ ⟨hbM, hbq⟩ ▸ hgT) hbT
            · rw [h] at hgv
              rcases (hcutp g).mp hgv with h' | h'
              · exact absurd (h' ▸ hgT) hbT
              · exact absurd (h' ▸ hgM) hfM
            · rw [h] at hgv
              exact hgru g ⟨hgM, hgv⟩
          obtain ⟨M'', hM'', hne''⟩ := key T p hTL hpT (by omega) honeT
          refine ep_blossom_lift α β L T p hpT M ?_ M'' hM'' hne''
          intro f' hf'T
          obtain ⟨v, u, hvT, huT, H⟩ := ep_ends_of_cross α β f' T hf'T
          have hf'b : f' ≠ b := fun h => hbT (h ▸ hf'T)
          have hf'f : f' ≠ f := fun h => hfT (h ▸ hf'T)
          have hf'p : ¬epCross α β {p} f' := fun h =>
            ((hcutp f').mp h).elim hf'b hf'f
          have hinside : ∀ g, (∀ c, epCross α β {c} g → c ∈ T) → α g ≠ β g →
              α g ∈ T ∧ β g ∈ T := fun g hg hne =>
            ⟨hg _ ((ep_cross_ends α β g hne _).mpr (Or.inl rfl)),
              hg _ ((ep_cross_ends α β g hne _).mpr (Or.inr rfl))⟩
          have hbin := hinside b (fun c hc => by
            rcases (Hb c).mp hc with h | h
            · exact h ▸ hpT
            · exact (hmemT c).mpr (Or.inl h)) (hM.1 b hbM)
          have hfin := hinside f (fun c hc => by
            rcases (Hf c).mp hc with h | h
            · exact h ▸ hpT
            · exact (hmemT c).mpr (Or.inr (Or.inr h))) hfnl
          have hvp : v ≠ p := fun h => hf'p (h ▸ (H v).mpr (Or.inl rfl))
          have hnot : ∀ c, c ∈ T → c ≠ v → ¬epCross α β {c} f' := by
            intro c hcT hcv hcr
            rcases (H c).mp hcr with h | h
            · exact hcv h
            · exact huT (h ▸ hcT)
          rcases (hmemT v).mp hvT with hv | hv | hv
          · -- `f'` ends at `q`: match `p` with `r` by `f`
            refine ⟨{f}, fun g hg => ?_, fun c hc => ?_⟩
            · rw [Finset.mem_singleton.mp hg]; exact ⟨hfin.1, hfin.2, hfnl⟩
            · rcases (hmemT c).mp hc with h | h | h
              · rw [h]
                exact (ep_exu2 f' f _ (hv ▸ (H v).mpr (Or.inl rfl)) hfq).1
              · rw [h]; exact (ep_exu2 f f' _ hfp hf'p).2
              · rw [h]
                exact (ep_exu2 f f' _ hfr (hnot r ((hmemT r).mpr (Or.inr (Or.inr rfl)))
                  (fun h' => hqr (hv ▸ h'.symm ▸ rfl)))).2
          · exact absurd hv hvp
          · -- `f'` ends at `r`: match `p` with `q` by `b`
            refine ⟨{b}, fun g hg => ?_, fun c hc => ?_⟩
            · rw [Finset.mem_singleton.mp hg]; exact ⟨hbin.1, hbin.2, hM.1 b hbM⟩
            · rcases (hmemT c).mp hc with h | h | h
              · rw [h]
                exact (ep_exu2 b f' _ hbq (hnot q ((hmemT q).mpr (Or.inl rfl))
                  (fun h' => hqr (h'.trans hv)))).2
              · rw [h]; exact (ep_exu2 b f' _ hbp hf'p).2
              · rw [h]
                exact (ep_exu2 f' b _ (hv ▸ (H v).mpr (Or.inl rfl)) hbr').1

open Classical in
/-- Cyclically 4-edge-connected (for cubic multigraphs): every proper nonempty vertex set has a
cut of size at least three, and every cut of size three has a side with a single vertex. -/
def EpCyc4 {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) : Prop :=
  (∀ T ⊆ L, T.Nonempty → T ≠ L → 3 ≤ (epCut α β T).card) ∧
    ∀ T ⊆ L, (epCut α β T).card = 3 → T.card = 1 ∨ (L \ T).card = 1

lemma EpCyc4.bridgeless {W E : Type*} [Fintype E] {α β : E → W} {L : Finset W}
    (hL : ∀ e, α e ∈ L ∧ β e ∈ L) (h : EpCyc4 α β L) : EpBridgeless α β L := by
  classical
  intro T hT h1
  by_cases hne : T.Nonempty
  · by_cases hTL : T = L
    · have : epCut α β T = ∅ := by
        ext e; rw [mem_epCut, hTL]; unfold epCross
        simp [(hL e).1, (hL e).2]
      rw [this] at h1; simp at h1
    · have := h.1 T hT hne hTL; omega
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    have : epCut α β T = ∅ := by
      ext e; rw [mem_epCut, hne]; unfold epCross; simp
    rw [this] at h1; simp at h1

open Classical in
/-- Ends after removing the vertices of `S`: edges meeting `S` become loops at `w₀`. -/
noncomputable def epRemA {W E : Type*} (α β : E → W) (S : Finset W) (w₀ : W) : E → W :=
  fun g => if α g ∈ S ∨ β g ∈ S then w₀ else α g

open Classical in
/-- See `epRemA`. -/
noncomputable def epRemB {W E : Type*} (α β : E → W) (S : Finset W) (w₀ : W) : E → W :=
  fun g => if α g ∈ S ∨ β g ∈ S then w₀ else β g

lemma epRem_cross {W E : Type*} (α β : E → W) (S : Finset W) (w₀ : W) (T : Finset W) (g : E) :
    epCross (epRemA α β S w₀) (epRemB α β S w₀) T g ↔
      ¬(α g ∈ S ∨ β g ∈ S) ∧ epCross α β T g := by
  classical
  unfold epCross epRemA epRemB
  by_cases h : α g ∈ S ∨ β g ∈ S
  · simp only [h, if_true, not_true_eq_false, false_and]; tauto
  · simp only [h, if_false, not_false_eq_true, true_and]

set_option maxHeartbeats 1600000 in
open Classical in
/-- **Lemma 22.** In a cubic cyclically 4-edge-connected multigraph with at least six vertices
every edge lies in at least two perfect matchings. -/
theorem ep_lemma22 {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (hc : EpCubic α β L) (h4 : EpCyc4 α β L) (h6 : 6 ≤ L.card) (e : E) :
    2 ≤ epMe α β L e := by
  have hL := hc.1
  have hb := h4.bridgeless hL
  obtain ⟨-, hpm⟩ := ep_cubic_edge_in_pm α β L hc.1 hc.2.1 hc.2.2 (fun T hT _ => hb T hT)
  obtain ⟨M, hM, heM⟩ := hpm e
  suffices hmain : ∃ M', M' ∈ epPM α β L ∧ e ∈ M' ∧ M' ≠ M by
    obtain ⟨M', hM', heM', hne⟩ := hmain
    unfold epMe
    exact Finset.one_lt_card.mpr ⟨M', Finset.mem_filter.mpr ⟨(mem_epPMs _ _ _ _).mpr hM', heM'⟩,
      M, Finset.mem_filter.mpr ⟨(mem_epPMs _ _ _ _).mpr hM, heM⟩, hne⟩
  have huv : α e ≠ β e := hc.2.1 e
  obtain ⟨S, hS⟩ : ∃ S : Finset W, S = {α e, β e} := ⟨_, rfl⟩
  have hmemS : ∀ x, x ∈ S ↔ x = α e ∨ x = β e := by intro x; rw [hS]; simp
  have hSL : S ⊆ L := by
    intro x hx; rcases (hmemS x).mp hx with h | h <;> rw [h]
    · exact (hL e).1
    · exact (hL e).2
  have hScard : S.card = 2 := by rw [hS]; exact Finset.card_pair huv
  have hL'card : (L \ S).card = L.card - 2 := by rw [Finset.card_sdiff_of_subset hSL, hScard]
  obtain ⟨w₀, hw₀⟩ : (L \ S).Nonempty := Finset.card_pos.mp (by omega)
  -- edges of `M` other than `e` avoid `S`
  have hecross : ∀ x, x ∈ S → epCross α β {x} e := fun x hx =>
    (ep_cross_ends α β e huv x).mpr ((hmemS x).mp hx)
  have hnt : ∀ g ∈ M, g ≠ e → ¬(α g ∈ S ∨ β g ∈ S) := by
    intro g hg hge h
    have hgn := hM.1 g hg
    rcases h with h | h
    · exact hge ((hM.2 _ (hSL h)).unique
        ⟨hg, (ep_cross_ends α β g hgn _).mpr (Or.inl rfl)⟩ ⟨heM, hecross _ h⟩)
    · exact hge ((hM.2 _ (hSL h)).unique
        ⟨hg, (ep_cross_ends α β g hgn _).mpr (Or.inr rfl)⟩ ⟨heM, hecross _ h⟩)
  have hL₂ : ∀ g, epRemA α β S w₀ g ∈ L \ S ∧ epRemB α β S w₀ g ∈ L \ S := by
    intro g
    unfold epRemA epRemB
    by_cases h : α g ∈ S ∨ β g ∈ S
    · rw [if_pos h, if_pos h]; exact ⟨hw₀, hw₀⟩
    · rw [if_neg h, if_neg h]
      push Not at h
      exact ⟨Finset.mem_sdiff.mpr ⟨(hL g).1, h.1⟩, Finset.mem_sdiff.mpr ⟨(hL g).2, h.2⟩⟩
  have hnoloop₂ : ∀ g, epRemA α β S w₀ g ≠ epRemB α β S w₀ g → ¬(α g ∈ S ∨ β g ∈ S) := by
    intro g hg h
    unfold epRemA epRemB at hg
    rw [if_pos h, if_pos h] at hg
    exact hg rfl
  have hM₂ : M.erase e ∈ epPM (epRemA α β S w₀) (epRemB α β S w₀) (L \ S) := by
    refine ⟨fun g hg => ?_, fun c hc' => ?_⟩
    · have h := hnt g (Finset.mem_of_mem_erase hg) (Finset.ne_of_mem_erase hg)
      unfold epRemA epRemB
      rw [if_neg h, if_neg h]
      exact hM.1 g (Finset.mem_of_mem_erase hg)
    · obtain ⟨g, ⟨h1, h2⟩, huniq⟩ := hM.2 c (Finset.mem_sdiff.mp hc').1
      have hge : g ≠ e := by
        intro h; rw [h] at h2
        rcases (ep_cross_ends α β e huv c).mp h2 with h' | h'
        · exact (Finset.mem_sdiff.mp hc').2 ((hmemS c).mpr (Or.inl h'))
        · exact (Finset.mem_sdiff.mp hc').2 ((hmemS c).mpr (Or.inr h'))
      refine ⟨g, ⟨Finset.mem_erase.mpr ⟨hge, h1⟩,
        (epRem_cross α β S w₀ {c} g).mpr ⟨hnt g h1 hge, h2⟩⟩, ?_⟩
      rintro g' ⟨hg', hc''⟩
      exact huniq g' ⟨Finset.mem_of_mem_erase hg', ((epRem_cross α β S w₀ {c} g').mp hc'').2⟩
  have hM₂ne : (M.erase e).Nonempty := by
    obtain ⟨g, ⟨h1, -⟩, -⟩ := hM₂.2 w₀ hw₀
    exact ⟨g, h1⟩
  by_cases hK : ∀ g ∈ M.erase e, ∀ T ⊆ L \ S,
      epCut (epRemA α β S w₀) (epRemB α β S w₀) T ≠ {g}
  · -- Kotzig gives a second perfect matching of `G - u - v`
    obtain ⟨N, hN, hNne⟩ := ep_kotzig _ (epRemA α β S w₀) (epRemB α β S w₀) (L \ S) rfl hL₂
      (M.erase e) hM₂ hM₂ne hK
    have hNnt : ∀ g ∈ N, ¬(α g ∈ S ∨ β g ∈ S) := fun g hg => hnoloop₂ g (hN.1 g hg)
    have heN : e ∉ N := fun h => hNnt e h (Or.inl ((hmemS _).mpr (Or.inl rfl)))
    refine ⟨insert e N, ⟨fun g hg => hc.2.1 g, fun c hcL => ?_⟩, Finset.mem_insert_self _ _, ?_⟩
    · by_cases hcS : c ∈ S
      · refine ⟨e, ⟨Finset.mem_insert_self _ _, hecross c hcS⟩, ?_⟩
        rintro g ⟨hg, hgc⟩
        rcases Finset.mem_insert.mp hg with h | h
        · exact h
        · exfalso
          apply hNnt g h
          rw [epCross_singleton] at hgc
          rcases hgc with ⟨h', -⟩ | ⟨-, h'⟩
          · exact Or.inl (h' ▸ hcS)
          · exact Or.inr (h' ▸ hcS)
      · obtain ⟨g, ⟨h1, h2⟩, huniq⟩ := hN.2 c (Finset.mem_sdiff.mpr ⟨hcL, hcS⟩)
        refine ⟨g, ⟨Finset.mem_insert_of_mem h1, ((epRem_cross α β S w₀ {c} g).mp h2).2⟩, ?_⟩
        rintro g' ⟨hg', hg'c⟩
        rcases Finset.mem_insert.mp hg' with h | h
        · exfalso
          rw [h] at hg'c
          rcases (ep_cross_ends α β e huv c).mp hg'c with h' | h'
          · exact hcS ((hmemS c).mpr (Or.inl h'))
          · exact hcS ((hmemS c).mpr (Or.inr h'))
        · exact huniq g' ⟨h, (epRem_cross α β S w₀ {c} g').mpr ⟨hNnt g' h, hg'c⟩⟩
    · intro h
      apply hNne
      rw [← h, Finset.erase_insert heN]
  · -- a bridge of `G - u - v` gives two cuts of size three with large sides
    exfalso
    push Not at hK
    obtain ⟨b, hbM, T, hTL', hT⟩ := hK
    have hcross₂ : ∀ T' g, g ∈ epCut (epRemA α β S w₀) (epRemB α β S w₀) T' ↔
        ¬(α g ∈ S ∨ β g ∈ S) ∧ epCross α β T' g := fun T' g => by
      rw [mem_epCut, epRem_cross]
    have hbT := (hcross₂ T b).mp (by rw [hT]; exact Finset.mem_singleton_self b)
    obtain ⟨B, hB⟩ : ∃ B : Finset W, B = (L \ S) \ T := ⟨_, rfl⟩
    have hmemB : ∀ x, x ∈ B ↔ (x ∈ L ∧ x ∉ S) ∧ x ∉ T := by
      intro x; rw [hB]; simp [Finset.mem_sdiff]
    have hTS : ∀ x, x ∈ T → x ∉ S := fun x hx => (Finset.mem_sdiff.mp (hTL' hx)).2
    have hTLx : ∀ x, x ∈ T → x ∈ L := fun x hx => (Finset.mem_sdiff.mp (hTL' hx)).1
    -- the cut of `B` in `G - u - v` is also `{b}`
    have hB₂ : epCut (epRemA α β S w₀) (epRemB α β S w₀) B = {b} := by
      rw [← hT]
      ext g
      rw [hcross₂, hcross₂]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        push Not at h1
        unfold epCross at h2 ⊢
        simp only [hmemB, (hL g).1, (hL g).2, h1.1, h1.2, not_false_eq_true, and_self,
          true_and] at h2
        tauto
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        push Not at h1
        unfold epCross at h2 ⊢
        simp only [hmemB, (hL g).1, (hL g).2, h1.1, h1.2, not_false_eq_true, and_self,
          true_and]
        tauto
    have hbB := (hcross₂ B b).mp (by rw [hB₂]; exact Finset.mem_singleton_self b)
    -- general bound for a set whose cut in `G - u - v` is `{b}`
    have hbound : ∀ T' : Finset W, (∀ x, x ∈ T' → x ∉ S) →
        epCut (epRemA α β S w₀) (epRemB α β S w₀) T' = {b} →
        epCut α β T' ⊆ insert b ((epCut α β S).filter (epCross α β T')) := by
      intro T' hT'S hT'cut g hg
      rw [Finset.mem_insert, Finset.mem_filter, mem_epCut]
      by_cases hgb : g = b
      · exact Or.inl hgb
      · right
        have hgc := (mem_epCut _ _ _ _).mp hg
        refine ⟨?_, hgc⟩
        have hnot : g ∉ epCut (epRemA α β S w₀) (epRemB α β S w₀) T' := by
          rw [hT'cut, Finset.mem_singleton]; exact hgb
        rw [hcross₂] at hnot
        have htouch : α g ∈ S ∨ β g ∈ S := by
          by_contra h; exact hnot ⟨h, hgc⟩
        unfold epCross at hgc ⊢
        have h1 := hT'S (α g); have h2 := hT'S (β g)
        tauto
    have hBS : ∀ x, x ∈ B → x ∉ S := fun x hx => ((hmemB x).mp hx).1.2
    have hsubT := hbound T hTS hT
    have hsubB := hbound B hBS hB₂
    have hdisj : Disjoint ((epCut α β S).filter (epCross α β T))
        ((epCut α β S).filter (epCross α β B)) := by
      rw [Finset.disjoint_left]
      intro g hg1 hg2
      rw [Finset.mem_filter, mem_epCut] at hg1 hg2
      have a1 := hTS (α g); have a2 := hTS (β g)
      have b1 := (hmemB (α g)).mp; have b2 := (hmemB (β g)).mp
      obtain ⟨hS1, hT1⟩ := hg1
      obtain ⟨-, hB1⟩ := hg2
      unfold epCross at hS1 hT1 hB1
      tauto
    have hSle : (epCut α β S).card ≤ 4 := by
      have hsub : epCut α β S ⊆ (epCut α β {α e} ∪ epCut α β {β e}).erase e := by
        intro g hg
        rw [mem_epCut] at hg
        rw [Finset.mem_erase, Finset.mem_union, mem_epCut, mem_epCut, epCross_singleton,
          epCross_singleton]
        unfold epCross at hg
        simp only [hmemS] at hg
        refine ⟨?_, ?_⟩
        · rintro rfl; tauto
        · tauto
      have he1 : e ∈ epCut α β {α e} := (mem_epCut _ _ _ _).mpr
        ((ep_cross_ends α β e huv _).mpr (Or.inl rfl))
      have he2 : e ∈ epCut α β {β e} := (mem_epCut _ _ _ _).mpr
        ((ep_cross_ends α β e huv _).mpr (Or.inr rfl))
      have hunion := Finset.card_union_add_card_inter (epCut α β {α e}) (epCut α β {β e})
      have hinter : 1 ≤ (epCut α β {α e} ∩ epCut α β {β e}).card :=
        Finset.card_pos.mpr ⟨e, Finset.mem_inter.mpr ⟨he1, he2⟩⟩
      have h3a := hc.2.2 _ (hL e).1
      have h3b := hc.2.2 _ (hL e).2
      have := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem (Finset.mem_union_left _ he1)] at this
      omega
    have hTne : T.Nonempty := by
      have := hbT.2; unfold epCross at this
      rcases this with ⟨h, -⟩ | ⟨-, h⟩ <;> exact ⟨_, h⟩
    have hBne : B.Nonempty := by
      have := hbB.2; unfold epCross at this
      rcases this with ⟨h, -⟩ | ⟨-, h⟩ <;> exact ⟨_, h⟩
    have hBL : B ⊆ L := fun x hx => ((hmemB x).mp hx).1.1
    have hTsub : T ⊆ L := fun x hx => hTLx x hx
    have hαS : α e ∈ S := (hmemS _).mpr (Or.inl rfl)
    have hTneL : T ≠ L := fun h => hTS _ (h ▸ (hL e).1) hαS
    have hBneL : B ≠ L := fun h => hBS _ (h ▸ (hL e).1) hαS
    have h3T := h4.1 T hTsub hTne hTneL
    have h3B := h4.1 B hBL hBne hBneL
    have hcT := Finset.card_le_card hsubT
    have hcB := Finset.card_le_card hsubB
    have hi1 := Finset.card_insert_le b ((epCut α β S).filter (epCross α β T))
    have hi2 := Finset.card_insert_le b ((epCut α β S).filter (epCross α β B))
    have hu : ((epCut α β S).filter (epCross α β T)).card +
        ((epCut α β S).filter (epCross α β B)).card ≤ (epCut α β S).card := by
      rw [← Finset.card_union_of_disjoint hdisj]
      exact Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _)
        (Finset.filter_subset _ _))
    have hT3 : (epCut α β T).card = 3 := by omega
    have hB3 : (epCut α β B).card = 3 := by omega
    -- both sides are single vertices
    have hTB : Disjoint T B := by
      rw [Finset.disjoint_left]; intro x hx hx'; exact ((hmemB x).mp hx').2 hx
    have hpart : L.card = S.card + T.card + B.card := by
      have : L = S ∪ T ∪ B := by
        ext x
        simp only [Finset.mem_union, hmemB]
        constructor
        · intro hx
          by_cases h1 : x ∈ S
          · exact Or.inl (Or.inl h1)
          · by_cases h2 : x ∈ T
            · exact Or.inl (Or.inr h2)
            · exact Or.inr ⟨⟨hx, h1⟩, h2⟩
        · rintro ((h | h) | h)
          · exact hSL h
          · exact hTLx x h
          · exact h.1.1
      have hST : Disjoint S T := by
        rw [Finset.disjoint_left]; intro x hx hx'; exact hTS x hx' hx
      have hSTB : Disjoint (S ∪ T) B := by
        rw [Finset.disjoint_left]; intro x hx hx'
        rcases Finset.mem_union.mp hx with h | h
        · exact hBS x hx' h
        · exact ((hmemB x).mp hx').2 h
      rw [this, Finset.card_union_of_disjoint hSTB, Finset.card_union_of_disjoint hST]
    have hTpos := Finset.card_pos.mpr hTne
    have hBpos := Finset.card_pos.mpr hBne
    have hT1 : T.card = 1 := by
      rcases h4.2 T hTsub hT3 with h | h
      · exact h
      · rw [Finset.card_sdiff_of_subset hTsub] at h; omega
    have hB1 : B.card = 1 := by
      rcases h4.2 B hBL hB3 with h | h
      · exact h
      · rw [Finset.card_sdiff_of_subset hBL] at h; omega
    omega

/-- A cubic multigraph with dead edges: every edge is live (both ends in `L`, not a loop) or
dead (a loop at a vertex outside `L`). Used for the results of contractions. -/
def EpCubicD {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) : Prop :=
  (∀ e, (α e ∈ L ∧ β e ∈ L ∧ α e ≠ β e) ∨ (α e ∉ L ∧ β e = α e)) ∧
    ∀ c ∈ L, (epCut α β {c}).card = 3

lemma EpCubic.toD {W E : Type*} [Fintype E] {α β : E → W} {L : Finset W}
    (h : EpCubic α β L) : EpCubicD α β L :=
  ⟨fun e => Or.inl ⟨(h.1 e).1, (h.1 e).2, h.2.1 e⟩, h.2.2⟩

/-- Dead edges cross no vertex set. -/
lemma epD_dead_not_cross {W E : Type*} (α β : E → W) (e : E) (h : β e = α e) (T : Finset W) :
    ¬epCross α β T e := by
  unfold epCross; rw [h]; tauto

/-- An edge crossing some set is live. -/
lemma epD_live_of_cross {W E : Type*} [Fintype E] {α β : E → W} {L : Finset W}
    (h : EpCubicD α β L) (T : Finset W) (e : E) (hc : epCross α β T e) :
    α e ∈ L ∧ β e ∈ L ∧ α e ≠ β e := by
  rcases h.1 e with h' | h'
  · exact h'
  · exact absurd hc (epD_dead_not_cross α β e h'.2 T)

/-- Perfect matchings contain only live edges. -/
lemma epD_live_of_mem_pm {W E : Type*} [Fintype E] {α β : E → W} {L : Finset W}
    (h : EpCubicD α β L) {M : Finset E} (hM : M ∈ epPM α β L) (e : E) (he : e ∈ M) :
    α e ∈ L ∧ β e ∈ L := by
  rcases h.1 e with h' | h'
  · exact ⟨h'.1, h'.2.1⟩
  · exact absurd h'.2.symm (hM.1 e he)

/-- Local matchings of `X ⊆ L` contain only live edges. -/
lemma epD_live_of_mem_lm {W E : Type*} [Fintype E] {α β : E → W} {L : Finset W}
    (h : EpCubicD α β L) (X : Finset W) (hX : X ⊆ L) {M : Finset E} (hM : M ∈ epLM α β X)
    (e : E) (he : e ∈ M) : α e ∈ L ∧ β e ∈ L := by
  rcases h.1 e with h' | h'
  · exact ⟨h'.1, h'.2.1⟩
  · exfalso
    rcases hM.1 e he with h'' | h''
    · exact h'.1 (hX h'')
    · exact h'.1 (h'.2 ▸ hX h'')

/-- Cuts computed on the live edges. -/
lemma epD_cut_card {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    [Fintype {e : E // α e ∈ L}] (h : EpCubicD α β L) (T : Finset W) :
    (epCut (fun e : {e : E // α e ∈ L} => α e.1) (fun e => β e.1) T).card =
      (epCut α β T).card := by
  classical
  refine Finset.card_bij (fun e _ => e.1) (fun e he => ?_) (fun a _ b _ h' => Subtype.ext h')
    (fun e he => ?_)
  · rw [mem_epCut] at he ⊢; exact he
  · rw [mem_epCut] at he
    exact ⟨⟨e, (epD_live_of_cross h T e he).1⟩, (mem_epCut _ _ _ _).mpr he, rfl⟩

/-- The live edges of a cubic multigraph with dead edges form a strict cubic multigraph. -/
lemma epD_live_cubic {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    [Fintype {e : E // α e ∈ L}] (h : EpCubicD α β L) :
    EpCubic (fun e : {e : E // α e ∈ L} => α e.1) (fun e => β e.1) L := by
  refine ⟨fun e => ?_, fun e => ?_, fun c hc => ?_⟩
  · rcases h.1 e.1 with h' | h'
    · exact ⟨h'.1, h'.2.1⟩
    · exact absurd e.2 h'.1
  · rcases h.1 e.1 with h' | h'
    · exact h'.2.2
    · exact absurd e.2 h'.1
  · rw [epD_cut_card α β L h {c}]; exact h.2 c hc

lemma epD_live_bridgeless {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    [Fintype {e : E // α e ∈ L}] (h : EpCubicD α β L) (hb : EpBridgeless α β L) :
    EpBridgeless (fun e : {e : E // α e ∈ L} => α e.1) (fun e => β e.1) L := by
  intro T hT
  rw [epD_cut_card α β L h T]; exact hb T hT

lemma epD_live_cyc4 {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    [Fintype {e : E // α e ∈ L}] (h : EpCubicD α β L) (h4 : EpCyc4 α β L) :
    EpCyc4 (fun e : {e : E // α e ∈ L} => α e.1) (fun e => β e.1) L := by
  refine ⟨fun T hT hne hTL => ?_, fun T hT h3 => ?_⟩
  · rw [epD_cut_card α β L h T]; exact h4.1 T hT hne hTL
  · rw [epD_cut_card α β L h T] at h3; exact h4.2 T hT h3

/-- A perfect matching of the live part gives a perfect matching of the whole multigraph. -/
lemma epD_pm_map {W E : Type*} [DecidableEq E] (α β : E → W) (L : Finset W)
    {N : Finset {e : E // α e ∈ L}}
    (hN : N ∈ epPM (fun e : {e : E // α e ∈ L} => α e.1) (fun e => β e.1) L) :
    N.map ⟨Subtype.val, Subtype.val_injective⟩ ∈ epPM α β L := by
  refine ⟨fun e he => ?_, fun c hc => ?_⟩
  · obtain ⟨e', he', rfl⟩ := Finset.mem_map.mp he
    exact hN.1 e' he'
  · obtain ⟨e₁, ⟨h1, h2⟩, huniq⟩ := hN.2 c hc
    refine ⟨e₁.1, ⟨Finset.mem_map.mpr ⟨e₁, h1, rfl⟩, h2⟩, ?_⟩
    rintro e ⟨he, hcr⟩
    obtain ⟨e', he', rfl⟩ := Finset.mem_map.mp he
    exact congrArg Subtype.val (huniq e' ⟨he', hcr⟩)

open Classical in
/-- In a cubic bridgeless multigraph with dead edges every live edge lies in a perfect
matching. -/
lemma epD_edge_in_pm {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (h : EpCubicD α β L) (hb : EpBridgeless α β L) (e : E) (he : α e ∈ L) :
    ∃ M, M ∈ epPM α β L ∧ e ∈ M := by
  have hc := epD_live_cubic α β L h
  have hb' := epD_live_bridgeless α β L h hb
  obtain ⟨-, hpm⟩ := ep_cubic_edge_in_pm _ _ L hc.1 hc.2.1 hc.2.2 (fun T hT _ => hb' T hT)
  obtain ⟨N, hN, heN⟩ := hpm ⟨e, he⟩
  exact ⟨_, epD_pm_map α β L hN, Finset.mem_map.mpr ⟨⟨e, he⟩, heN, rfl⟩⟩

/-- Two perfect matchings through an edge, from `epMe ≥ 2`. -/
lemma epMe_two {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (e : E)
    (h2 : 2 ≤ epMe α β L e) :
    ∃ M₁ M₂, M₁ ∈ epPM α β L ∧ M₂ ∈ epPM α β L ∧ M₁ ≠ M₂ ∧ e ∈ M₁ ∧ e ∈ M₂ := by
  classical
  unfold epMe at h2
  obtain ⟨N₁, hN₁, N₂, hN₂, hne⟩ := Finset.one_lt_card.mp h2
  have a1 := Finset.mem_filter.mp hN₁
  have a2 := Finset.mem_filter.mp hN₂
  exact ⟨N₁, N₂, (mem_epPMs _ _ _ _).mp a1.1, (mem_epPMs _ _ _ _).mp a2.1, hne, a1.2, a2.2⟩

open Classical in
/-- **Lemma 22 with dead edges.** Every live edge of a cubic cyclically 4-edge-connected
multigraph with at least six vertices lies in two distinct perfect matchings. -/
lemma epD_lemma22 {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (h : EpCubicD α β L) (h4 : EpCyc4 α β L) (h6 : 6 ≤ L.card) (e : E) (he : α e ∈ L) :
    ∃ M₁ M₂, M₁ ∈ epPM α β L ∧ M₂ ∈ epPM α β L ∧ M₁ ≠ M₂ ∧ e ∈ M₁ ∧ e ∈ M₂ := by
  obtain ⟨N₁, N₂, hN₁, hN₂, hne, h1, h2⟩ := epMe_two _ _ L _
    (ep_lemma22 _ _ L (epD_live_cubic α β L h) (epD_live_cyc4 α β L h h4) h6 ⟨e, he⟩)
  refine ⟨_, _, epD_pm_map α β L hN₁, epD_pm_map α β L hN₂, ?_,
    Finset.mem_map.mpr ⟨⟨e, he⟩, h1, rfl⟩, Finset.mem_map.mpr ⟨⟨e, he⟩, h2, rfl⟩⟩
  intro heq
  exact hne (Finset.map_injective _ heq)

open Classical in
/-- Contraction of a vertex set `X` to `x₀ ∈ X` for cubic multigraphs with dead edges:
edges inside `X` become dead loops at the removed vertex `x₁ ∈ X`, `x₁ ≠ x₀`. First end. -/
noncomputable def epConA {W E : Type*} (α β : E → W) (X : Finset W) (x₀ x₁ : W) : E → W :=
  fun e => if α e ∈ X ∧ β e ∈ X then x₁ else epRho X x₀ (α e)

open Classical in
/-- See `epConA`. Second end. -/
noncomputable def epConB {W E : Type*} (α β : E → W) (X : Finset W) (x₀ x₁ : W) : E → W :=
  fun e => if α e ∈ X ∧ β e ∈ X then x₁ else epRho X x₀ (β e)

lemma epCon_cross {W E : Type*} (α β : E → W) (L X : Finset W) (x₀ x₁ : W) (hx₀ : x₀ ∈ X)
    (T' : Finset W) (hT' : T' ⊆ epL' L X x₀) (e : E) :
    epCross (epConA α β X x₀ x₁) (epConB α β X x₀ x₁) T' e ↔
      epCross α β (epLift X x₀ T') e := by
  classical
  by_cases hin : α e ∈ X ∧ β e ∈ X
  · have h1 : ¬epCross (epConA α β X x₀ x₁) (epConB α β X x₀ x₁) T' e := by
      unfold epCross epConA epConB
      rw [if_pos hin, if_pos hin]; tauto
    have h2 : ¬epCross α β (epLift X x₀ T') e := by
      unfold epCross epLift
      split_ifs with h
      · simp only [Finset.mem_union, hin.1, hin.2, or_true, not_true_eq_false, and_false,
          false_and, or_self, not_false_eq_true]
      · have hno : ∀ w, w ∈ X → w ∉ T' := by
          intro w hw hwT
          have := hT' hwT
          unfold epL' at this
          rw [Finset.mem_insert, Finset.mem_sdiff] at this
          rcases this with rfl | ⟨-, h'⟩
          · exact h hwT
          · exact h' hw
        have a1 := hno _ hin.1; have a2 := hno _ hin.2
        tauto
    exact iff_of_false h1 h2
  · rw [← epCross_contract α β L X x₀ hx₀ T' hT' e]
    unfold epCross epConA epConB
    rw [if_neg hin, if_neg hin]

lemma epCon_cut {W E : Type*} [Fintype E] (α β : E → W) (L X : Finset W) (x₀ x₁ : W)
    (hx₀ : x₀ ∈ X) (T' : Finset W) (hT' : T' ⊆ epL' L X x₀) :
    epCut (epConA α β X x₀ x₁) (epConB α β X x₀ x₁) T' = epCut α β (epLift X x₀ T') := by
  ext e
  rw [mem_epCut, mem_epCut, epCon_cross α β L X x₀ x₁ hx₀ T' hT']

/-- **Lemma 7(1), 3-edge-cuts.** Contracting a side of a cut of size three in a cubic bridgeless
multigraph gives a cubic bridgeless multigraph. -/
lemma epCon_cubic {W E : Type*} [Fintype E] (α β : E → W) (L X : Finset W) (x₀ x₁ : W)
    (h : EpCubicD α β L) (hb : EpBridgeless α β L) (hXL : X ⊆ L) (hx₀ : x₀ ∈ X) (hx₁ : x₁ ∈ X)
    (hne : x₁ ≠ x₀) (h3 : (epCut α β X).card = 3) :
    EpCubicD (epConA α β X x₀ x₁) (epConB α β X x₀ x₁) (epL' L X x₀) ∧
      EpBridgeless (epConA α β X x₀ x₁) (epConB α β X x₀ x₁) (epL' L X x₀) := by
  classical
  have hx₁L' : x₁ ∉ epL' L X x₀ := by
    unfold epL'
    rw [Finset.mem_insert, Finset.mem_sdiff]
    rintro (h' | ⟨-, h'⟩)
    · exact hne h'
    · exact h' hx₁
  refine ⟨⟨fun e => ?_, fun c hc => ?_⟩, fun T' hT' => ?_⟩
  · by_cases hin : α e ∈ X ∧ β e ∈ X
    · right
      unfold epConA epConB
      rw [if_pos hin, if_pos hin]
      exact ⟨hx₁L', rfl⟩
    · unfold epConA epConB
      rw [if_neg hin, if_neg hin]
      rcases h.1 e with ⟨h1, h2, h3'⟩ | ⟨h1, h2⟩
      · left
        refine ⟨epRho_mem_L' L X x₀ _ h1, epRho_mem_L' L X x₀ _ h2, ?_⟩
        intro heq
        unfold epRho at heq
        by_cases ha : α e ∈ X <;> by_cases hb' : β e ∈ X
        · exact hin ⟨ha, hb'⟩
        · rw [if_pos ha, if_neg hb'] at heq; exact hb' (heq ▸ hx₀)
        · rw [if_neg ha, if_pos hb'] at heq; exact ha (heq.symm ▸ hx₀)
        · rw [if_neg ha, if_neg hb'] at heq; exact h3' heq
      · right
        have ha : α e ∉ X := fun h' => h1 (hXL h')
        have hb' : β e ∉ X := fun h' => h1 (h2 ▸ hXL h')
        unfold epRho
        rw [if_neg ha, if_neg hb']
        refine ⟨?_, h2⟩
        unfold epL'
        rw [Finset.mem_insert, Finset.mem_sdiff]
        rintro (h' | ⟨h', -⟩)
        · exact h1 (h' ▸ hXL hx₀)
        · exact h1 h'
  · rw [epCon_cut α β L X x₀ x₁ hx₀ {c} (Finset.singleton_subset_iff.mpr hc)]
    by_cases hct : c = x₀
    · rw [hct, epLift_singleton_t₀ X x₀ hx₀]; exact h3
    · rw [epLift_singleton_ne X x₀ c hct]
      unfold epL' at hc
      rw [Finset.mem_insert, Finset.mem_sdiff] at hc
      rcases hc with h' | ⟨h', -⟩
      · exact absurd h' hct
      · exact h.2 c h'
  · rw [epCon_cut α β L X x₀ x₁ hx₀ T' hT']
    exact hb _ (epLift_subset L X x₀ hXL hx₀ T' hT')

open Classical in
/-- The end of an edge outside `X` (for an edge crossing `X`). -/
noncomputable def epOut {W E : Type*} (α β : E → W) (X : Finset W) (g : E) : W :=
  if α g ∈ X then β g else α g

lemma epOut_spec {W E : Type*} (α β : E → W) (X : Finset W) (g : E) (h : epCross α β X g) :
    epOut α β X g ∉ X ∧
      ((α g ∈ X ∧ β g = epOut α β X g) ∨ (β g ∈ X ∧ α g = epOut α β X g)) := by
  classical
  unfold epOut
  unfold epCross at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [if_pos h1]; exact ⟨h2, Or.inl ⟨h1, rfl⟩⟩
  · rw [if_neg h1]; exact ⟨h1, Or.inr ⟨h2, rfl⟩⟩

open Classical in
/-- Contraction of a 2-edge-cut `δ(X) = {e, e'}` by redirection: `X` is removed, `e` becomes the
new edge joining the outside ends of `e` and `e'`, and `e'` and the edges inside `X` become dead
loops at the removed vertex `x₁ ∈ X`. First end. -/
noncomputable def ep2A {W E : Type*} (α β : E → W) (X : Finset W) (e e' : E) (x₁ : W) : E → W :=
  fun g => if g = e then epOut α β X e
    else if g = e' ∨ (α g ∈ X ∧ β g ∈ X) then x₁ else α g

open Classical in
/-- See `ep2A`. Second end. -/
noncomputable def ep2B {W E : Type*} (α β : E → W) (X : Finset W) (e e' : E) (x₁ : W) : E → W :=
  fun g => if g = e then epOut α β X e'
    else if g = e' ∨ (α g ∈ X ∧ β g ∈ X) then x₁ else β g

open Classical in
/-- The preimage of a vertex set of the 2-cut contraction. -/
noncomputable def ep2Lift {W : Type*} (X : Finset W) (a' : W) (T' : Finset W) : Finset W :=
  if a' ∈ T' then T' ∪ X else T'

lemma ep_cross_pq {W E : Type*} (α β : E → W) (g : E) (p q : W)
    (h : (α g = p ∧ β g = q) ∨ (α g = q ∧ β g = p)) (S : Finset W) :
    epCross α β S g ↔ (p ∈ S ∧ q ∉ S) ∨ (p ∉ S ∧ q ∈ S) := by
  unfold epCross
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2]; tauto

/-- A crossing edge has an end `x ∈ X` and the end `epOut`. -/
lemma epOut_ends {W E : Type*} (α β : E → W) (X : Finset W) (g : E) (h : epCross α β X g) :
    epOut α β X g ∉ X ∧ ∃ x, x ∈ X ∧
      ((α g = x ∧ β g = epOut α β X g) ∨ (α g = epOut α β X g ∧ β g = x)) := by
  obtain ⟨h1, h2⟩ := epOut_spec α β X g h
  refine ⟨h1, ?_⟩
  rcases h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · exact ⟨α g, h3, Or.inl ⟨rfl, h4⟩⟩
  · exact ⟨β g, h3, Or.inr ⟨h4, rfl⟩⟩

set_option maxHeartbeats 800000 in
/-- Cuts of the 2-cut contraction are cuts of the original multigraph. -/
lemma ep2_cross {W E : Type*} (α β : E → W) (X : Finset W) (e e' : E) (x₁ : W)
    (hcut : ∀ g, epCross α β X g ↔ g = e ∨ g = e') (T' : Finset W)
    (hT' : ∀ w, w ∈ T' → w ∉ X) (g : E) :
    epCross (ep2A α β X e e' x₁) (ep2B α β X e e' x₁) T' g ↔
      epCross α β (ep2Lift X (epOut α β X e') T') g := by
  classical
  obtain ⟨ha, x, hx, hex⟩ := epOut_ends α β X e ((hcut e).mpr (Or.inl rfl))
  obtain ⟨ha', x', hx', hex'⟩ := epOut_ends α β X e' ((hcut e').mpr (Or.inr rfl))
  have hA : ∀ g, ep2A α β X e e' x₁ g = if g = e then epOut α β X e
      else if g = e' ∨ (α g ∈ X ∧ β g ∈ X) then x₁ else α g := fun _ => rfl
  have hB : ∀ g, ep2B α β X e e' x₁ g = if g = e then epOut α β X e'
      else if g = e' ∨ (α g ∈ X ∧ β g ∈ X) then x₁ else β g := fun _ => rfl
  have hLift : ep2Lift X (epOut α β X e') T' =
      if epOut α β X e' ∈ T' then T' ∪ X else T' := rfl
  generalize epOut α β X e = a at *
  generalize epOut α β X e' = a' at *
  have hxT : x ∉ T' := fun h => hT' x h hx
  have hx'T : x' ∉ T' := fun h => hT' x' h hx'
  have hlhs : epCross (ep2A α β X e e' x₁) (ep2B α β X e e' x₁) T' g ↔
      (ep2A α β X e e' x₁ g ∈ T' ∧ ep2B α β X e e' x₁ g ∉ T') ∨
        (ep2A α β X e e' x₁ g ∉ T' ∧ ep2B α β X e e' x₁ g ∈ T') := Iff.rfl
  rw [hlhs, hA, hB, hLift]
  by_cases hg : g = e
  · rw [if_pos hg, if_pos hg, hg, ep_cross_pq α β e x a hex]
    by_cases h : a' ∈ T'
    · rw [if_pos h]
      have m1 : x ∈ T' ∪ X := Finset.mem_union_right _ hx
      by_cases hP : a ∈ T'
      · have m2 : a ∈ T' ∪ X := Finset.mem_union_left _ hP
        simp [h, hP, m1, m2]
      · have m2 : a ∉ T' ∪ X := fun h' => (Finset.mem_union.mp h').elim hP ha
        simp [h, hP, m1, m2]
    · rw [if_neg h]
      by_cases hP : a ∈ T' <;> simp [h, hP, hxT]
  · rw [if_neg hg, if_neg hg]
    by_cases hg' : g = e' ∨ (α g ∈ X ∧ β g ∈ X)
    · rw [if_pos hg', if_pos hg']
      have hl : ¬((x₁ ∈ T' ∧ x₁ ∉ T') ∨ (x₁ ∉ T' ∧ x₁ ∈ T')) := by
        rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact h2 h1
        · exact h1 h2
      refine iff_of_false hl ?_
      rcases hg' with hge' | ⟨h1, h2⟩
      · rw [hge', ep_cross_pq α β e' x' a' hex']
        by_cases h : a' ∈ T'
        · rw [if_pos h]
          have m1 : x' ∈ T' ∪ X := Finset.mem_union_right _ hx'
          have m2 : a' ∈ T' ∪ X := Finset.mem_union_left _ h
          simp [m1, m2]
        · rw [if_neg h]; simp [h, hx'T]
      · by_cases h : a' ∈ T'
        · rw [if_pos h]
          have m1 : α g ∈ T' ∪ X := Finset.mem_union_right _ h1
          have m2 : β g ∈ T' ∪ X := Finset.mem_union_right _ h2
          unfold epCross; simp [m1, m2]
        · rw [if_neg h]
          have m1 : α g ∉ T' := fun h' => hT' (α g) h' h1
          have m2 : β g ∉ T' := fun h' => hT' (β g) h' h2
          unfold epCross; simp [m1, m2]
    · rw [if_neg hg', if_neg hg']
      push Not at hg'
      have hnc : ¬epCross α β X g := fun h => by
        rcases (hcut g).mp h with h' | h'
        · exact hg h'
        · exact hg'.1 h'
      have hαX : α g ∉ X := by
        intro h1
        exact hnc (Or.inl ⟨h1, hg'.2 h1⟩)
      have hβX : β g ∉ X := by
        intro h1
        exact hnc (Or.inr ⟨hαX, h1⟩)
      by_cases h : a' ∈ T'
      · rw [if_pos h]
        have m1 : α g ∈ T' ∪ X ↔ α g ∈ T' := by
          rw [Finset.mem_union]; exact ⟨fun h' => h'.elim id (fun h'' => absurd h'' hαX), Or.inl⟩
        have m2 : β g ∈ T' ∪ X ↔ β g ∈ T' := by
          rw [Finset.mem_union]; exact ⟨fun h' => h'.elim id (fun h'' => absurd h'' hβX), Or.inl⟩
        unfold epCross
        rw [m1, m2]
      · rw [if_neg h]; rfl

lemma ep2_cut {W E : Type*} [Fintype E] (α β : E → W) (X : Finset W) (e e' : E) (x₁ : W)
    (hcut : ∀ g, epCross α β X g ↔ g = e ∨ g = e') (T' : Finset W)
    (hT' : ∀ w, w ∈ T' → w ∉ X) :
    epCut (ep2A α β X e e' x₁) (ep2B α β X e e' x₁) T' =
      epCut α β (ep2Lift X (epOut α β X e') T') := by
  ext g
  rw [mem_epCut, mem_epCut, ep2_cross α β X e e' x₁ hcut T' hT']

open Classical in
/-- In a cubic multigraph with dead edges, odd sets have odd cuts. -/
lemma epD_cut_odd {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (h : EpCubicD α β L)
    (T : Finset W) (hT : T ⊆ L) (hodd : Odd T.card) : Odd (epCut α β T).card := by
  have hc := epD_live_cubic α β L h
  rw [← epD_cut_card α β L h T]
  exact ep_cubic_cut_odd _ _ L hc.2.1 hc.2.2 T hT hodd

lemma ep_cut_insert_subset {W E : Type*} [Fintype E] [DecidableEq W] [DecidableEq E]
    (α β : E → W) (X : Finset W) (v : W) :
    epCut α β (insert v X) ⊆ epCut α β X ∪ epCut α β {v} := by
  intro g hg
  rw [Finset.mem_union, mem_epCut, mem_epCut, epCross_singleton]
  rw [mem_epCut] at hg
  unfold epCross at hg ⊢
  simp only [Finset.mem_insert] at hg
  by_cases h1 : α g ∈ X <;> by_cases h2 : β g ∈ X <;> by_cases h3 : α g = v <;>
    by_cases h4 : β g = v <;> simp_all

set_option maxHeartbeats 800000 in
open Classical in
/-- Adding to `X` the outside end `v` of a cut edge `e₁`: bound on the new cut. -/
lemma ep_cut_insert_card {W E : Type*} [Fintype E] (α β : E → W) (L X : Finset W)
    (h : EpCubicD α β L) (hb : EpBridgeless α β L) (hXL : X ⊆ L) (e e' : E) (hee' : e ≠ e')
    (hcut : ∀ g, epCross α β X g ↔ g = e ∨ g = e') (e₁ : E) (he₁ : e₁ = e ∨ e₁ = e') :
    epOut α β X e₁ ∈ L ∧ epOut α β X e₁ ∉ X ∧
      (epCut α β (insert (epOut α β X e₁) X)).card = 3 ∧
      ∀ e₂, (e₂ = e ∨ e₂ = e') → e₂ ≠ e₁ → epOut α β X e₂ ≠ epOut α β X e₁ := by
  have hcr₁ : epCross α β X e₁ := (hcut e₁).mpr he₁
  obtain ⟨hv, x, hx, hends⟩ := epOut_ends α β X e₁ hcr₁
  have hlive := epD_live_of_cross h X e₁ hcr₁
  generalize epOut α β X e₁ = v at *
  have hvL : v ∈ L := by
    rcases hends with ⟨-, h2⟩ | ⟨h1, -⟩
    · rw [← h2]; exact hlive.2.1
    · rw [← h1]; exact hlive.1
  have hxv : x ≠ v := fun h' => hv (h' ▸ hx)
  -- the cut of `X` has two elements, so `|X|` is even and `|X ∪ {v}|` is odd
  have hcutX : epCut α β X = {e, e'} := by
    ext g; rw [mem_epCut, hcut, Finset.mem_insert, Finset.mem_singleton]
  have hXeven : ¬Odd X.card := by
    intro ho
    have := epD_cut_odd α β L h X hXL ho
    rw [hcutX, Finset.card_pair hee'] at this
    exact absurd this (by decide)
  have hTL : insert v X ⊆ L := Finset.insert_subset hvL hXL
  have hTodd : Odd (insert v X).card := by
    rw [Finset.card_insert_of_notMem hv]
    rcases Nat.even_or_odd X.card with he | ho
    · exact he.add_one
    · exact absurd ho hXeven
  have hodd := epD_cut_odd α β L h _ hTL hTodd
  -- `e₁` does not cross `X ∪ {v}` and lies in both cuts
  have he₁T : e₁ ∉ epCut α β (insert v X) := by
    rw [mem_epCut, ep_cross_pq α β e₁ x v hends]
    simp [hx]
  have he₁X : e₁ ∈ epCut α β X := (mem_epCut _ _ _ _).mpr hcr₁
  have he₁v : e₁ ∈ epCut α β {v} := by
    rw [mem_epCut, ep_cross_pq α β e₁ x v hends]
    simp [hxv]
  have hsub : epCut α β (insert v X) ⊆ (epCut α β X ∪ epCut α β {v}).erase e₁ := by
    intro g hg
    exact Finset.mem_erase.mpr ⟨fun h' => he₁T (h' ▸ hg), ep_cut_insert_subset α β X v hg⟩
  have hunion := Finset.card_union_add_card_inter (epCut α β X) (epCut α β {v})
  have hinter : 1 ≤ (epCut α β X ∩ epCut α β {v}).card :=
    Finset.card_pos.mpr ⟨e₁, Finset.mem_inter.mpr ⟨he₁X, he₁v⟩⟩
  have h2 : (epCut α β X).card = 2 := by rw [hcutX, Finset.card_pair hee']
  have h3 := h.2 v hvL
  have hle := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_union_left _ he₁X)] at hle
  have hne1 := hb _ hTL
  have hcard3 : (epCut α β (insert v X)).card = 3 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  refine ⟨hvL, hv, hcard3, ?_⟩
  intro e₂ he₂ hne heq
  -- then `e₂` also lies in both cuts and does not cross `X ∪ {v}`: the cut would be too small
  have hcr₂ : epCross α β X e₂ := (hcut e₂).mpr he₂
  obtain ⟨-, x₂, hx₂, hends₂⟩ := epOut_ends α β X e₂ hcr₂
  rw [heq] at hends₂
  have hx₂v : x₂ ≠ v := fun h' => hv (h' ▸ hx₂)
  have he₂T : e₂ ∉ epCut α β (insert v X) := by
    rw [mem_epCut, ep_cross_pq α β e₂ x₂ v hends₂]
    simp [hx₂]
  have he₂X : e₂ ∈ epCut α β X := (mem_epCut _ _ _ _).mpr hcr₂
  have he₂v : e₂ ∈ epCut α β {v} := by
    rw [mem_epCut, ep_cross_pq α β e₂ x₂ v hends₂]
    simp [hx₂v]
  have hsub' : epCut α β (insert v X) ⊆
      ((epCut α β X ∪ epCut α β {v}).erase e₁).erase e₂ := by
    intro g hg
    exact Finset.mem_erase.mpr ⟨fun h' => he₂T (h' ▸ hg), hsub hg⟩
  have hinter2 : 2 ≤ (epCut α β X ∩ epCut α β {v}).card :=
    Finset.one_lt_card.mpr ⟨e₁, Finset.mem_inter.mpr ⟨he₁X, he₁v⟩, e₂,
      Finset.mem_inter.mpr ⟨he₂X, he₂v⟩, Ne.symm hne⟩
  have hle' := Finset.card_le_card hsub'
  rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr
    ⟨hne, Finset.mem_union_left _ he₂X⟩),
    Finset.card_erase_of_mem (Finset.mem_union_left _ he₁X)] at hle'
  omega

set_option maxHeartbeats 800000 in
open Classical in
/-- **Lemma 7(1), 2-edge-cuts.** Contracting a side of a cut of size two by redirection gives a
cubic bridgeless multigraph (with dead edges) on `L \ X`. -/
lemma ep2_cubic {W E : Type*} [Fintype E] (α β : E → W) (L X : Finset W) (e e' : E) (x₁ : W)
    (h : EpCubicD α β L) (hb : EpBridgeless α β L) (hXL : X ⊆ L) (hx₁ : x₁ ∈ X)
    (hee' : e ≠ e') (hcut : ∀ g, epCross α β X g ↔ g = e ∨ g = e') :
    EpCubicD (ep2A α β X e e' x₁) (ep2B α β X e e' x₁) (L \ X) ∧
      EpBridgeless (ep2A α β X e e' x₁) (ep2B α β X e e' x₁) (L \ X) := by
  obtain ⟨haL, haX, -, hne1⟩ := ep_cut_insert_card α β L X h hb hXL e e' hee' hcut e (Or.inl rfl)
  obtain ⟨ha'L, ha'X, h3', -⟩ :=
    ep_cut_insert_card α β L X h hb hXL e e' hee' hcut e' (Or.inr rfl)
  have haa' : epOut α β X e ≠ epOut α β X e' :=
    fun h' => hne1 e' (Or.inr rfl) (Ne.symm hee') h'.symm
  have hx₁' : x₁ ∉ L \ X := fun h' => (Finset.mem_sdiff.mp h').2 hx₁
  have hsub : ∀ T' : Finset W, T' ⊆ L \ X → ∀ w, w ∈ T' → w ∉ X :=
    fun T' hT' w hw => (Finset.mem_sdiff.mp (hT' hw)).2
  have hliftL : ∀ T' : Finset W, T' ⊆ L \ X → ep2Lift X (epOut α β X e') T' ⊆ L := by
    intro T' hT'
    have h1 : T' ⊆ L := fun w hw => (Finset.mem_sdiff.mp (hT' hw)).1
    unfold ep2Lift
    split_ifs
    · exact Finset.union_subset h1 hXL
    · exact h1
  refine ⟨⟨fun g => ?_, fun c hc => ?_⟩, fun T' hT' => ?_⟩
  · by_cases hg : g = e
    · left
      unfold ep2A ep2B
      rw [if_pos hg, if_pos hg]
      exact ⟨Finset.mem_sdiff.mpr ⟨haL, haX⟩, Finset.mem_sdiff.mpr ⟨ha'L, ha'X⟩, haa'⟩
    · by_cases hg' : g = e' ∨ (α g ∈ X ∧ β g ∈ X)
      · right
        unfold ep2A ep2B
        rw [if_neg hg, if_neg hg, if_pos hg', if_pos hg']
        exact ⟨hx₁', rfl⟩
      · unfold ep2A ep2B
        rw [if_neg hg, if_neg hg, if_neg hg', if_neg hg']
        push Not at hg'
        have hnc : ¬epCross α β X g := fun h' => by
          rcases (hcut g).mp h' with h'' | h''
          · exact hg h''
          · exact hg'.1 h''
        have hαX : α g ∉ X := fun h1 => hnc (Or.inl ⟨h1, hg'.2 h1⟩)
        have hβX : β g ∉ X := fun h1 => hnc (Or.inr ⟨hαX, h1⟩)
        rcases h.1 g with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨Finset.mem_sdiff.mpr ⟨h1, hαX⟩, Finset.mem_sdiff.mpr ⟨h2, hβX⟩, h3⟩
        · exact Or.inr ⟨fun h' => h1 (Finset.mem_sdiff.mp h').1, h2⟩
  · have hcX : c ∉ X := (Finset.mem_sdiff.mp hc).2
    rw [ep2_cut α β X e e' x₁ hcut {c} (fun w hw => by
      rw [Finset.mem_singleton.mp hw]; exact hcX)]
    unfold ep2Lift
    by_cases hca : epOut α β X e' ∈ ({c} : Finset W)
    · rw [if_pos hca]
      have : ({c} : Finset W) ∪ X = insert (epOut α β X e') X := by
        rw [Finset.mem_singleton.mp hca]; rfl
      rw [this]; exact h3'
    · rw [if_neg hca]; exact h.2 c (Finset.mem_sdiff.mp hc).1
  · rw [ep2_cut α β X e e' x₁ hcut T' (hsub T' hT')]
    exact hb _ (hliftL T' hT')

set_option maxHeartbeats 1600000 in
open Classical in
/-- One side of the matching correspondence for the 2-cut contraction by redirection: an edge set
`M` of `G` that agrees with a perfect matching `N` of the contraction outside `X` (where `e'` is
in `M` exactly when the new edge `e` is in `N`) meets every vertex of `L \ X` exactly once. -/
lemma ep2_side {W E : Type*} [Fintype E] (α β : E → W) (L X : Finset W) (e e' : E) (x₁ : W)
    (h : EpCubicD α β L) (hb : EpBridgeless α β L) (hXL : X ⊆ L)
    (hee' : e ≠ e') (hcut : ∀ g, epCross α β X g ↔ g = e ∨ g = e')
    (N : Finset E) (hN : N ∈ epPM (ep2A α β X e e' x₁) (ep2B α β X e e' x₁) (L \ X))
    (M : Finset E)
    (hM1 : ∀ g, g ≠ e → g ≠ e' → ¬(α g ∈ X ∧ β g ∈ X) → (g ∈ M ↔ g ∈ N))
    (hM2 : e ∈ M ↔ e ∈ N) (hM3 : e' ∈ M ↔ e ∈ N) (c : W) (hc : c ∈ L \ X) :
    ∃! g, g ∈ M ∧ epCross α β {c} g := by
  obtain ⟨-, -, -, hne1⟩ := ep_cut_insert_card α β L X h hb hXL e e' hee' hcut e (Or.inl rfl)
  have haa' : epOut α β X e ≠ epOut α β X e' :=
    fun h' => hne1 e' (Or.inr rfl) (Ne.symm hee') h'.symm
  obtain ⟨ha, x, hx, hex⟩ := epOut_ends α β X e ((hcut e).mpr (Or.inl rfl))
  obtain ⟨ha', x', hx', hex'⟩ := epOut_ends α β X e' ((hcut e').mpr (Or.inr rfl))
  have hcX : c ∉ X := (Finset.mem_sdiff.mp hc).2
  have hA : ∀ g, ep2A α β X e e' x₁ g = if g = e then epOut α β X e
      else if g = e' ∨ (α g ∈ X ∧ β g ∈ X) then x₁ else α g := fun _ => rfl
  have hB : ∀ g, ep2B α β X e e' x₁ g = if g = e then epOut α β X e'
      else if g = e' ∨ (α g ∈ X ∧ β g ∈ X) then x₁ else β g := fun _ => rfl
  generalize epOut α β X e = a at *
  generalize epOut α β X e' = a' at *
  have hxc : x ≠ c := fun h' => hcX (h' ▸ hx)
  have hx'c : x' ≠ c := fun h' => hcX (h' ▸ hx')
  -- crossing `{c}` in the contraction
  have cr_e : epCross (ep2A α β X e e' x₁) (ep2B α β X e e' x₁) {c} e ↔ (c = a ∨ c = a') := by
    rw [epCross_singleton, hA, hB, if_pos rfl, if_pos rfl]
    constructor
    · rintro (⟨h1, -⟩ | ⟨-, h2⟩)
      · exact Or.inl h1.symm
      · exact Or.inr h2.symm
    · rintro (h1 | h1)
      · exact Or.inl ⟨h1.symm, fun h2 => haa' (h1.symm.trans h2.symm).symm.symm⟩
      · exact Or.inr ⟨fun h2 => haa' (h2.trans h1), h1.symm⟩
  have cr_dead : ∀ g, g ≠ e → (g = e' ∨ (α g ∈ X ∧ β g ∈ X)) →
      ¬epCross (ep2A α β X e e' x₁) (ep2B α β X e e' x₁) {c} g := by
    intro g hg hg'
    rw [epCross_singleton, hA, hB, if_neg hg, if_neg hg, if_pos hg', if_pos hg']
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact h2 h1
    · exact h1 h2
  have cr_other : ∀ g, g ≠ e → ¬(g = e' ∨ (α g ∈ X ∧ β g ∈ X)) →
      (epCross (ep2A α β X e e' x₁) (ep2B α β X e e' x₁) {c} g ↔ epCross α β {c} g) := by
    intro g hg hg'
    rw [epCross_singleton, epCross_singleton, hA, hB, if_neg hg, if_neg hg, if_neg hg',
      if_neg hg']
  -- crossing `{c}` in `G`
  have g_e : epCross α β {c} e ↔ c = a := by
    rw [ep_cross_pq α β e x a hex]
    simp only [Finset.mem_singleton]
    constructor
    · rintro (⟨h1, -⟩ | ⟨-, h2⟩)
      · exact absurd h1 hxc
      · exact h2.symm
    · intro h1; exact Or.inr ⟨hxc, h1.symm⟩
  have g_e' : epCross α β {c} e' ↔ c = a' := by
    rw [ep_cross_pq α β e' x' a' hex']
    simp only [Finset.mem_singleton]
    constructor
    · rintro (⟨h1, -⟩ | ⟨-, h2⟩)
      · exact absurd h1 hx'c
      · exact h2.symm
    · intro h1; exact Or.inr ⟨hx'c, h1.symm⟩
  have g_in : ∀ g, (α g ∈ X ∧ β g ∈ X) → ¬epCross α β {c} g := by
    intro g hg hcr
    rw [epCross_singleton] at hcr
    rcases hcr with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact hcX (h1 ▸ hg.1)
    · exact hcX (h2 ▸ hg.2)
  obtain ⟨g₀, ⟨hg₀N, hg₀c⟩, huniq⟩ := hN.2 c hc
  by_cases hg₀ : g₀ = e
  · rw [hg₀] at hg₀N hg₀c
    rcases cr_e.mp hg₀c with hca | hca
    · refine ⟨e, ⟨hM2.mpr hg₀N, g_e.mpr hca⟩, ?_⟩
      rintro g ⟨hgM, hgc⟩
      by_contra hge
      by_cases hge' : g = e'
      · rw [hge'] at hgc
        exact haa' (hca.symm.trans (g_e'.mp hgc))
      · have hnin : ¬(α g ∈ X ∧ β g ∈ X) := fun h' => g_in g h' hgc
        have hgN := (hM1 g hge hge' hnin).mp hgM
        have := huniq g ⟨hgN, (cr_other g hge (fun h' => h'.elim hge' hnin)).mpr hgc⟩
        exact hge (this.trans hg₀)
    · refine ⟨e', ⟨hM3.mpr hg₀N, g_e'.mpr hca⟩, ?_⟩
      rintro g ⟨hgM, hgc⟩
      by_contra hge'
      by_cases hge : g = e
      · rw [hge] at hgc
        exact haa' ((g_e.mp hgc).symm.trans hca)
      · have hnin : ¬(α g ∈ X ∧ β g ∈ X) := fun h' => g_in g h' hgc
        have hgN := (hM1 g hge hge' hnin).mp hgM
        have := huniq g ⟨hgN, (cr_other g hge (fun h' => h'.elim hge' hnin)).mpr hgc⟩
        exact hge (this.trans hg₀)
  · have hnd : ¬(g₀ = e' ∨ (α g₀ ∈ X ∧ β g₀ ∈ X)) := fun h' => cr_dead g₀ hg₀ h' hg₀c
    push Not at hnd
    have hg₀G : epCross α β {c} g₀ :=
      (cr_other g₀ hg₀ (fun h' => h'.elim hnd.1 (fun h'' => hnd.2 h''.1 h''.2))).mp hg₀c
    have hnin : ¬(α g₀ ∈ X ∧ β g₀ ∈ X) := fun h' => hnd.2 h'.1 h'.2
    refine ⟨g₀, ⟨(hM1 g₀ hg₀ hnd.1 hnin).mpr hg₀N, hg₀G⟩, ?_⟩
    rintro g ⟨hgM, hgc⟩
    by_cases hge : g = e
    · rw [hge] at hgM hgc
      exact absurd (huniq e ⟨hM2.mp hgM, cr_e.mpr (Or.inl (g_e.mp hgc))⟩).symm hg₀
    · by_cases hge' : g = e'
      · rw [hge'] at hgM hgc
        exact absurd (huniq e ⟨hM3.mp hgM, cr_e.mpr (Or.inr (g_e'.mp hgc))⟩).symm hg₀
      · have hnin' : ¬(α g ∈ X ∧ β g ∈ X) := fun h' => g_in g h' hgc
        exact huniq g ⟨(hM1 g hge hge' hnin').mp hgM,
          (cr_other g hge (fun h' => h'.elim hge' hnin')).mpr hgc⟩

/-- Edges of a perfect matching of the 2-cut contraction: the new edge, or an untouched edge. -/
lemma ep2_pm_edge {W E : Type*} (α β : E → W) (L X : Finset W) (e e' : E) (x₁ : W)
    {N : Finset E} (hN : N ∈ epPM (ep2A α β X e e' x₁) (ep2B α β X e e' x₁) L) (g : E)
    (hg : g ∈ N) : g = e ∨ (g ≠ e ∧ g ≠ e' ∧ ¬(α g ∈ X ∧ β g ∈ X) ∧ α g ≠ β g) := by
  classical
  by_cases hge : g = e
  · exact Or.inl hge
  · right
    have hnl := hN.1 g hg
    have hA : ep2A α β X e e' x₁ g = if g = e then epOut α β X e
        else if g = e' ∨ (α g ∈ X ∧ β g ∈ X) then x₁ else α g := rfl
    have hB : ep2B α β X e e' x₁ g = if g = e then epOut α β X e'
        else if g = e' ∨ (α g ∈ X ∧ β g ∈ X) then x₁ else β g := rfl
    rw [hA, hB, if_neg hge, if_neg hge] at hnl
    by_cases hd : g = e' ∨ (α g ∈ X ∧ β g ∈ X)
    · rw [if_pos hd, if_pos hd] at hnl; exact absurd rfl hnl
    · rw [if_neg hd, if_neg hd] at hnl
      exact ⟨hge, fun h' => hd (Or.inl h'), fun h' => hd (Or.inr h'), hnl⟩

set_option maxHeartbeats 1600000 in
open Classical in
/-- **Matching correspondence for 2-cut contraction by redirection (gluing direction).**
Let `δ(X) = {e, e'}`, `Y = L \ X`. A perfect matching `N₁` of the contraction that keeps `X` and
a perfect matching `N₂` of the contraction that keeps `Y`, which agree on the new edge `e`, glue
to a perfect matching of `G`: `N₁ ∪ N₂`, together with `e'` when the new edge is used. -/
lemma ep2_glue {W E : Type*} [Fintype E] (α β : E → W) (L X Y : Finset W) (e e' : E)
    (x₁ y₁ : W) (h : EpCubicD α β L) (hb : EpBridgeless α β L) (hXL : X ⊆ L)
    (hY : ∀ w, w ∈ Y ↔ w ∈ L ∧ w ∉ X) (hee' : e ≠ e')
    (hcut : ∀ g, epCross α β X g ↔ g = e ∨ g = e')
    (N₁ N₂ : Finset E)
    (hN₁ : N₁ ∈ epPM (ep2A α β Y e e' y₁) (ep2B α β Y e e' y₁) (L \ Y))
    (hN₂ : N₂ ∈ epPM (ep2A α β X e e' x₁) (ep2B α β X e e' x₁) (L \ X))
    (hiff : e ∈ N₁ ↔ e ∈ N₂) :
    N₁ ∪ N₂ ∪ (if e ∈ N₁ then {e'} else ∅) ∈ epPM α β L := by
  have hYL : Y ⊆ L := fun w hw => ((hY w).mp hw).1
  have hlive : ∀ g, α g ≠ β g → α g ∈ L ∧ β g ∈ L := by
    intro g hg
    rcases h.1 g with h' | h'
    · exact ⟨h'.1, h'.2.1⟩
    · exact absurd h'.2.symm hg
  have hcutY : ∀ g, epCross α β Y g ↔ g = e ∨ g = e' := by
    intro g
    by_cases hg : α g = β g
    · have h1 : ¬epCross α β Y g := by unfold epCross; rw [hg]; tauto
      have h2 : ¬epCross α β X g := by unfold epCross; rw [hg]; tauto
      rw [← hcut g]; exact iff_of_false h1 h2
    · rw [← hcut g]
      have := hlive g hg
      unfold epCross
      simp only [hY, this.1, this.2, true_and]
      tauto
  -- edges of `N₁` other than `e` lie inside `X`, those of `N₂` inside `Y`
  have hin₂ : ∀ g ∈ N₂, g ≠ e → g ≠ e' ∧ α g ≠ β g ∧ α g ∉ X ∧ β g ∉ X := by
    intro g hg hge
    rcases ep2_pm_edge α β (L \ X) X e e' x₁ hN₂ g hg with h' | ⟨-, h2, h3, h4⟩
    · exact absurd h' hge
    · have hnc : ¬epCross α β X g := fun hc => ((hcut g).mp hc).elim hge h2
      unfold epCross at hnc
      exact ⟨h2, h4, by tauto, by tauto⟩
  have hin₁ : ∀ g ∈ N₁, g ≠ e → g ≠ e' ∧ α g ≠ β g ∧ α g ∈ X ∧ β g ∈ X := by
    intro g hg hge
    rcases ep2_pm_edge α β (L \ Y) Y e e' y₁ hN₁ g hg with h' | ⟨-, h2, h3, h4⟩
    · exact absurd h' hge
    · have hnc : ¬epCross α β Y g := fun hc => ((hcutY g).mp hc).elim hge h2
      have hl := hlive g h4
      have a1 := hY (α g); have a2 := hY (β g)
      unfold epCross at hnc
      exact ⟨h2, h4, by tauto, by tauto⟩
  have he'₁ : e' ∉ N₁ := fun h' =>
    (ep2_pm_edge α β (L \ Y) Y e e' y₁ hN₁ e' h').elim (fun h'' => hee' h''.symm)
      (fun h'' => h''.2.1 rfl)
  have he'₂ : e' ∉ N₂ := fun h' =>
    (ep2_pm_edge α β (L \ X) X e e' x₁ hN₂ e' h').elim (fun h'' => hee' h''.symm)
      (fun h'' => h''.2.1 rfl)
  have hmemM : ∀ g, g ∈ N₁ ∪ N₂ ∪ (if e ∈ N₁ then {e'} else ∅) ↔
      g ∈ N₁ ∨ g ∈ N₂ ∨ (g = e' ∧ e ∈ N₁) := by
    intro g
    rw [Finset.mem_union, Finset.mem_union]
    by_cases he : e ∈ N₁
    · rw [if_pos he, Finset.mem_singleton]; tauto
    · rw [if_neg he]; simp [he]
  have hne : α e ≠ β e := by
    have := (hcut e).mpr (Or.inl rfl)
    unfold epCross at this
    intro h'; rw [h'] at this; tauto
  have hne' : α e' ≠ β e' := by
    have := (hcut e').mpr (Or.inr rfl)
    unfold epCross at this
    intro h'; rw [h'] at this; tauto
  refine ⟨fun g hg => ?_, fun c hc => ?_⟩
  · rcases (hmemM g).mp hg with h' | h' | ⟨h', -⟩
    · by_cases hge : g = e
      · rw [hge]; exact hne
      · exact (hin₁ g h' hge).2.1
    · by_cases hge : g = e
      · rw [hge]; exact hne
      · exact (hin₂ g h' hge).2.1
    · rw [h']; exact hne'
  · by_cases hcX : c ∈ X
    · -- the vertex lies in `X`: use the contraction that removes `Y`
      have hcY : c ∉ Y := fun h' => ((hY c).mp h').2 hcX
      refine ep2_side α β L Y e e' y₁ h hb hYL hee' hcutY N₁ hN₁ _ ?_ ?_ ?_ c
        (Finset.mem_sdiff.mpr ⟨hc, hcY⟩)
      · intro g hge hge' hnin
        rw [hmemM]
        constructor
        · rintro (h' | h' | ⟨h', -⟩)
          · exact h'
          · exfalso
            have := hin₂ g h' hge
            have hl := hlive g this.2.1
            exact hnin ⟨(hY _).mpr ⟨hl.1, this.2.2.1⟩, (hY _).mpr ⟨hl.2, this.2.2.2⟩⟩
          · exact absurd h' hge'
        · exact Or.inl
      · rw [hmemM]
        constructor
        · rintro (h' | h' | ⟨h', -⟩)
          · exact h'
          · exact hiff.mpr h'
          · exact absurd h' hee'
        · exact Or.inl
      · rw [hmemM]
        constructor
        · rintro (h' | h' | ⟨-, h'⟩)
          · exact absurd h' he'₁
          · exact absurd h' he'₂
          · exact h'
        · intro h'; exact Or.inr (Or.inr ⟨rfl, h'⟩)
    · refine ep2_side α β L X e e' x₁ h hb hXL hee' hcut N₂ hN₂ _ ?_ ?_ ?_ c
        (Finset.mem_sdiff.mpr ⟨hc, hcX⟩)
      · intro g hge hge' hnin
        rw [hmemM]
        constructor
        · rintro (h' | h' | ⟨h', -⟩)
          · exfalso
            have := hin₁ g h' hge
            exact hnin ⟨this.2.2.1, this.2.2.2⟩
          · exact h'
          · exact absurd h' hge'
        · intro h'; exact Or.inr (Or.inl h')
      · rw [hmemM]
        constructor
        · rintro (h' | h' | ⟨h', -⟩)
          · exact hiff.mp h'
          · exact h'
          · exact absurd h' hee'
        · intro h'; exact Or.inr (Or.inl h')
      · rw [hmemM]
        constructor
        · rintro (h' | h' | ⟨-, h'⟩)
          · exact absurd h' he'₁
          · exact absurd h' he'₂
          · exact hiff.mp h'
        · intro h'; exact Or.inr (Or.inr ⟨rfl, hiff.mpr h'⟩)

open Classical in
/-- The glued edge set of `ep2_glue`. -/
noncomputable def ep2Glue {E : Type*} (e e' : E) (N₁ N₂ : Finset E) : Finset E :=
  N₁ ∪ N₂ ∪ (if e ∈ N₁ then {e'} else ∅)

lemma ep2_cut_compl {W E : Type*} [Fintype E] (α β : E → W) (L X Y : Finset W) (e e' : E)
    (h : EpCubicD α β L) (hY : ∀ w, w ∈ Y ↔ w ∈ L ∧ w ∉ X)
    (hcut : ∀ g, epCross α β X g ↔ g = e ∨ g = e') (g : E) :
    epCross α β Y g ↔ g = e ∨ g = e' := by
  by_cases hg : α g = β g
  · have h1 : ¬epCross α β Y g := by unfold epCross; rw [hg]; tauto
    have h2 : ¬epCross α β X g := by unfold epCross; rw [hg]; tauto
    rw [← hcut g]; exact iff_of_false h1 h2
  · rw [← hcut g]
    have hl : α g ∈ L ∧ β g ∈ L := by
      rcases h.1 g with h' | h'
      · exact ⟨h'.1, h'.2.1⟩
      · exact absurd h'.2.symm hg
    unfold epCross
    simp only [hY, hl.1, hl.2, true_and]
    tauto

/-- Edges other than `e` of a perfect matching of the 2-cut contraction avoid `X`. -/
lemma ep2_pm_outside {W E : Type*} (α β : E → W) (L' X : Finset W) (e e' : E) (x₁ : W)
    (hcut : ∀ g, epCross α β X g ↔ g = e ∨ g = e')
    {N : Finset E} (hN : N ∈ epPM (ep2A α β X e e' x₁) (ep2B α β X e e' x₁) L') (g : E)
    (hg : g ∈ N) (hge : g ≠ e) : g ≠ e' ∧ α g ≠ β g ∧ α g ∉ X ∧ β g ∉ X := by
  rcases ep2_pm_edge α β L' X e e' x₁ hN g hg with h' | ⟨-, h2, h3, h4⟩
  · exact absurd h' hge
  · have hnc : ¬epCross α β X g := fun hc => ((hcut g).mp hc).elim hge h2
    have ha : α g ∉ X := fun h1 => hnc (Or.inl ⟨h1, fun h2' => h3 ⟨h1, h2'⟩⟩)
    have hb : β g ∉ X := fun h1 => hnc (Or.inr ⟨ha, h1⟩)
    exact ⟨h2, h4, ha, hb⟩

open Classical in
/-- The glued matching determines the matching of the contraction that removes `X`. -/
lemma ep2_glue_filter {W E : Type*} [Fintype E] (α β : E → W) (L X Y : Finset W) (e e' : E)
    (x₁ y₁ : W) (h : EpCubicD α β L) (hY : ∀ w, w ∈ Y ↔ w ∈ L ∧ w ∉ X) (hee' : e ≠ e')
    (hcut : ∀ g, epCross α β X g ↔ g = e ∨ g = e')
    (N₁ N₂ : Finset E)
    (hN₁ : N₁ ∈ epPM (ep2A α β Y e e' y₁) (ep2B α β Y e e' y₁) (L \ Y))
    (hN₂ : N₂ ∈ epPM (ep2A α β X e e' x₁) (ep2B α β X e e' x₁) (L \ X))
    (hiff : e ∈ N₁ ↔ e ∈ N₂) :
    (ep2Glue e e' N₁ N₂).filter (fun g => g ≠ e' ∧ ¬(α g ∈ X ∧ β g ∈ X)) = N₂ := by
  have hcutY := ep2_cut_compl α β L X Y e e' h hY hcut
  have heX : ¬(α e ∈ X ∧ β e ∈ X) := by
    have := (hcut e).mpr (Or.inl rfl)
    unfold epCross at this; tauto
  ext g
  unfold ep2Glue
  rw [Finset.mem_filter, Finset.mem_union, Finset.mem_union]
  constructor
  · rintro ⟨(hg | hg) | hg, hne', hnin⟩
    · by_cases hge : g = e
      · rw [hge]; rw [hge] at hg; exact hiff.mp hg
      · exfalso
        have a := ep2_pm_outside α β (L \ Y) Y e e' y₁ hcutY hN₁ g hg hge
        have hl : α g ∈ L ∧ β g ∈ L := by
          rcases h.1 g with h' | h'
          · exact ⟨h'.1, h'.2.1⟩
          · exact absurd h'.2.symm a.2.1
        have b1 := hY (α g); have b2 := hY (β g)
        exact hnin ⟨by tauto, by tauto⟩
    · exact hg
    · exfalso
      split_ifs at hg
      · exact hne' (Finset.mem_singleton.mp hg)
      · exact absurd hg (Finset.notMem_empty g)
  · intro hg
    refine ⟨Or.inl (Or.inr hg), ?_, ?_⟩
    · by_cases hge : g = e
      · rw [hge]; exact hee'
      · exact (ep2_pm_outside α β (L \ X) X e e' x₁ hcut hN₂ g hg hge).1
    · by_cases hge : g = e
      · rw [hge]; exact heX
      · have a := ep2_pm_outside α β (L \ X) X e e' x₁ hcut hN₂ g hg hge
        exact fun h' => a.2.2.1 h'.1

open Classical in
lemma ep2Glue_comm {E : Type*} (e e' : E) (N₁ N₂ : Finset E) (hiff : e ∈ N₁ ↔ e ∈ N₂) :
    ep2Glue e e' N₁ N₂ = ep2Glue e e' N₂ N₁ := by
  unfold ep2Glue
  rw [Finset.union_comm N₁ N₂]
  by_cases h : e ∈ N₁
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]

set_option maxHeartbeats 1600000 in
open Classical in
/-- **Lemma 7(2) for 2-cuts, edges inside `Y`.** -/
lemma ep2_count_side {W E : Type*} [Fintype E] (α β : E → W) (L X Y : Finset W) (e e' : E)
    (x₁ y₁ : W) (h : EpCubicD α β L) (hb : EpBridgeless α β L) (hXL : X ⊆ L)
    (hY : ∀ w, w ∈ Y ↔ w ∈ L ∧ w ∉ X) (hy₁ : y₁ ∈ Y) (hee' : e ≠ e')
    (hcut : ∀ g, epCross α β X g ↔ g = e ∨ g = e') (k₁ k₂ : ℕ)
    (h₁ : ∀ g, ep2A α β Y e e' y₁ g ∈ L \ Y →
      k₁ ≤ epMe (ep2A α β Y e e' y₁) (ep2B α β Y e e' y₁) (L \ Y) g)
    (g : E) (h₂ : k₂ ≤ epMe (ep2A α β X e e' x₁) (ep2B α β X e e' x₁) (L \ X) g) :
    k₁ * k₂ ≤ epMe α β L g := by
  have hYL : Y ⊆ L := fun w hw => ((hY w).mp hw).1
  have hX : ∀ w, w ∈ X ↔ w ∈ L ∧ w ∉ Y := by
    intro w
    constructor
    · intro hw; exact ⟨hXL hw, fun h' => ((hY w).mp h').2 hw⟩
    · rintro ⟨h1, h2⟩; by_contra h'; exact h2 ((hY w).mpr ⟨h1, h'⟩)
  have hcutY := ep2_cut_compl α β L X Y e e' h hY hcut
  obtain ⟨hcub₁, -⟩ := ep2_cubic α β L Y e e' y₁ h hb hYL hy₁ hee' hcutY
  -- the new edge is live in the contraction keeping `X`
  have helive : ep2A α β Y e e' y₁ e ∈ L \ Y ∧ ep2B α β Y e e' y₁ e ∈ L \ Y ∧
      ep2A α β Y e e' y₁ e ≠ ep2B α β Y e e' y₁ e := by
    rcases hcub₁.1 e with h' | h'
    · exact h'
    · exfalso
      have hA : ep2A α β Y e e' y₁ e = epOut α β Y e := by unfold ep2A; rw [if_pos rfl]
      obtain ⟨hb1, hb2, -, -⟩ := ep_cut_insert_card α β L Y h hb hYL e e' hee' hcutY e
        (Or.inl rfl)
      exact h'.1 (hA ▸ Finset.mem_sdiff.mpr ⟨hb1, hb2⟩)
  obtain ⟨b, hbdef⟩ : ∃ b, b = ep2A α β Y e e' y₁ e := ⟨_, rfl⟩
  have hbL : b ∈ L \ Y := hbdef ▸ helive.1
  have hecr : epCross (ep2A α β Y e e' y₁) (ep2B α β Y e e' y₁) {b} e := by
    rw [ep_cross_ends _ _ e helive.2.2]; exact Or.inl hbdef
  have hcard := hcub₁.2 b hbL
  obtain ⟨f, hfcut, hfe⟩ : ∃ f ∈ epCut (ep2A α β Y e e' y₁) (ep2B α β Y e e' y₁) {b}, f ≠ e :=
    Finset.exists_mem_ne (by omega) e
  have hfcr := (mem_epCut _ _ _ _).mp hfcut
  have hflive := (epD_live_of_cross hcub₁ {b} f hfcr).1
  -- the three families of perfect matchings
  obtain ⟨Pin, hPin⟩ : ∃ P : Finset (Finset E), P =
      (epPMs (ep2A α β Y e e' y₁) (ep2B α β Y e e' y₁) (L \ Y)).filter (fun N => e ∈ N) :=
    ⟨_, rfl⟩
  obtain ⟨Pout, hPout⟩ : ∃ P : Finset (Finset E), P =
      (epPMs (ep2A α β Y e e' y₁) (ep2B α β Y e e' y₁) (L \ Y)).filter (fun N => f ∈ N) :=
    ⟨_, rfl⟩
  obtain ⟨S₂, hS₂⟩ : ∃ P : Finset (Finset E), P =
      (epPMs (ep2A α β X e e' x₁) (ep2B α β X e e' x₁) (L \ X)).filter (fun N => g ∈ N) :=
    ⟨_, rfl⟩
  have hPin_card : k₁ ≤ Pin.card := by rw [hPin]; exact h₁ e helive.1
  have hPout_card : k₁ ≤ Pout.card := by rw [hPout]; exact h₁ f hflive
  have hS₂_card : k₂ ≤ S₂.card := by rw [hS₂]; exact h₂
  have hPin_mem : ∀ N, N ∈ Pin →
      N ∈ epPM (ep2A α β Y e e' y₁) (ep2B α β Y e e' y₁) (L \ Y) ∧ e ∈ N := by
    intro N hN; rw [hPin, Finset.mem_filter, mem_epPMs] at hN; exact hN
  have hPout_mem : ∀ N, N ∈ Pout →
      N ∈ epPM (ep2A α β Y e e' y₁) (ep2B α β Y e e' y₁) (L \ Y) ∧ e ∉ N := by
    intro N hN
    rw [hPout, Finset.mem_filter, mem_epPMs] at hN
    refine ⟨hN.1, fun he => hfe ?_⟩
    exact (hN.1.2 b hbL).unique ⟨hN.2, hfcr⟩ ⟨he, hecr⟩
  have hS₂_mem : ∀ N, N ∈ S₂ →
      N ∈ epPM (ep2A α β X e e' x₁) (ep2B α β X e e' x₁) (L \ X) ∧ g ∈ N := by
    intro N hN; rw [hS₂, Finset.mem_filter, mem_epPMs] at hN; exact hN
  -- valid pairs
  have hvalid : ∀ p ∈ S₂.sigma (fun N₂ => if e ∈ N₂ then Pin else Pout),
      p.2 ∈ epPM (ep2A α β Y e e' y₁) (ep2B α β Y e e' y₁) (L \ Y) ∧
        p.1 ∈ epPM (ep2A α β X e e' x₁) (ep2B α β X e e' x₁) (L \ X) ∧ g ∈ p.1 ∧
        (e ∈ p.2 ↔ e ∈ p.1) := by
    rintro ⟨N₂, N₁⟩ hp
    rw [Finset.mem_sigma] at hp
    obtain ⟨hp1, hp2⟩ := hp
    have a := hS₂_mem N₂ hp1
    by_cases he : e ∈ N₂
    · rw [if_pos he] at hp2
      have b' := hPin_mem N₁ hp2
      exact ⟨b'.1, a.1, a.2, ⟨fun _ => he, fun _ => b'.2⟩⟩
    · rw [if_neg he] at hp2
      have b' := hPout_mem N₁ hp2
      exact ⟨b'.1, a.1, a.2, ⟨fun h' => absurd h' b'.2, fun h' => absurd h' he⟩⟩
  have hinj : Set.InjOn (fun p : (_ : Finset E) × Finset E => ep2Glue e e' p.2 p.1)
      ↑(S₂.sigma (fun N₂ => if e ∈ N₂ then Pin else Pout)) := by
    rintro ⟨N₂, N₁⟩ hp ⟨N₂', N₁'⟩ hp' heq
    obtain ⟨a1, a2, -, a4⟩ := hvalid _ (Finset.mem_coe.mp hp)
    obtain ⟨b1, b2, -, b4⟩ := hvalid _ (Finset.mem_coe.mp hp')
    dsimp only at heq a1 a2 a4 b1 b2 b4
    have e2 : N₂ = N₂' := by
      rw [← ep2_glue_filter α β L X Y e e' x₁ y₁ h hY hee' hcut N₁ N₂ a1 a2 a4,
        ← ep2_glue_filter α β L X Y e e' x₁ y₁ h hY hee' hcut N₁' N₂' b1 b2 b4, heq]
    have e1 : N₁ = N₁' := by
      rw [← ep2_glue_filter α β L Y X e e' y₁ x₁ h hX hee' hcutY N₂ N₁ a2 a1 a4.symm,
        ← ep2_glue_filter α β L Y X e e' y₁ x₁ h hX hee' hcutY N₂' N₁' b2 b1 b4.symm,
        ← ep2Glue_comm e e' N₁ N₂ a4, ← ep2Glue_comm e e' N₁' N₂' b4, heq]
    rw [e1, e2]
  have hmaps : ∀ p ∈ (↑(S₂.sigma (fun N₂ => if e ∈ N₂ then Pin else Pout)) :
      Set ((_ : Finset E) × Finset E)),
      ep2Glue e e' p.2 p.1 ∈ ((epPMs α β L).filter (fun M => g ∈ M) : Finset (Finset E)) := by
    intro p hp
    obtain ⟨a1, a2, a3, a4⟩ := hvalid p (Finset.mem_coe.mp hp)
    rw [Finset.mem_filter, mem_epPMs]
    refine ⟨ep2_glue α β L X Y e e' x₁ y₁ h hb hXL hY hee' hcut p.2 p.1 a1 a2 a4, ?_⟩
    unfold ep2Glue
    exact Finset.mem_union_left _ (Finset.mem_union_right _ a3)
  have hle := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Finset.card_sigma] at hle
  have hsum : S₂.card • k₁ ≤ ∑ N₂ ∈ S₂, (if e ∈ N₂ then Pin else Pout).card := by
    refine Finset.card_nsmul_le_sum _ _ _ (fun N₂ _ => ?_)
    split_ifs
    · exact hPin_card
    · exact hPout_card
  rw [smul_eq_mul] at hsum
  unfold epMe
  calc k₁ * k₂ ≤ S₂.card * k₁ := by rw [mul_comm]; exact Nat.mul_le_mul_right _ hS₂_card
    _ ≤ _ := hsum.trans hle

set_option maxHeartbeats 1600000 in
open Classical in
/-- **Lemma 7(2) for 2-cuts, the cut edges.** -/
lemma ep2_count_cross {W E : Type*} [Fintype E] (α β : E → W) (L X Y : Finset W) (e e' : E)
    (x₁ y₁ : W) (h : EpCubicD α β L) (hb : EpBridgeless α β L) (hXL : X ⊆ L)
    (hY : ∀ w, w ∈ Y ↔ w ∈ L ∧ w ∉ X) (hee' : e ≠ e')
    (hcut : ∀ g, epCross α β X g ↔ g = e ∨ g = e') (k₁ k₂ : ℕ)
    (h₁ : k₁ ≤ epMe (ep2A α β Y e e' y₁) (ep2B α β Y e e' y₁) (L \ Y) e)
    (h₂ : k₂ ≤ epMe (ep2A α β X e e' x₁) (ep2B α β X e e' x₁) (L \ X) e)
    (g : E) (hg : g = e ∨ g = e') : k₁ * k₂ ≤ epMe α β L g := by
  have hX : ∀ w, w ∈ X ↔ w ∈ L ∧ w ∉ Y := by
    intro w
    constructor
    · intro hw; exact ⟨hXL hw, fun h' => ((hY w).mp h').2 hw⟩
    · rintro ⟨h1, h2⟩; by_contra h'; exact h2 ((hY w).mpr ⟨h1, h'⟩)
  have hcutY := ep2_cut_compl α β L X Y e e' h hY hcut
  obtain ⟨P₁, hP₁⟩ : ∃ P : Finset (Finset E), P =
      (epPMs (ep2A α β Y e e' y₁) (ep2B α β Y e e' y₁) (L \ Y)).filter (fun N => e ∈ N) :=
    ⟨_, rfl⟩
  obtain ⟨P₂, hP₂⟩ : ∃ P : Finset (Finset E), P =
      (epPMs (ep2A α β X e e' x₁) (ep2B α β X e e' x₁) (L \ X)).filter (fun N => e ∈ N) :=
    ⟨_, rfl⟩
  have hP₁c : k₁ ≤ P₁.card := by rw [hP₁]; exact h₁
  have hP₂c : k₂ ≤ P₂.card := by rw [hP₂]; exact h₂
  have hvalid : ∀ p ∈ P₁ ×ˢ P₂,
      p.1 ∈ epPM (ep2A α β Y e e' y₁) (ep2B α β Y e e' y₁) (L \ Y) ∧
        p.2 ∈ epPM (ep2A α β X e e' x₁) (ep2B α β X e e' x₁) (L \ X) ∧ e ∈ p.1 ∧ e ∈ p.2 := by
    rintro ⟨N₁, N₂⟩ hp
    rw [Finset.mem_product, hP₁, hP₂, Finset.mem_filter, Finset.mem_filter, mem_epPMs,
      mem_epPMs] at hp
    exact ⟨hp.1.1, hp.2.1, hp.1.2, hp.2.2⟩
  have hinj : Set.InjOn (fun p : Finset E × Finset E => ep2Glue e e' p.1 p.2) ↑(P₁ ×ˢ P₂) := by
    rintro ⟨N₁, N₂⟩ hp ⟨N₁', N₂'⟩ hp' heq
    obtain ⟨a1, a2, a3, a4⟩ := hvalid _ (Finset.mem_coe.mp hp)
    obtain ⟨b1, b2, b3, b4⟩ := hvalid _ (Finset.mem_coe.mp hp')
    dsimp only at heq a1 a2 a3 a4 b1 b2 b3 b4
    have a5 : e ∈ N₁ ↔ e ∈ N₂ := ⟨fun _ => a4, fun _ => a3⟩
    have b5 : e ∈ N₁' ↔ e ∈ N₂' := ⟨fun _ => b4, fun _ => b3⟩
    have e2 : N₂ = N₂' := by
      rw [← ep2_glue_filter α β L X Y e e' x₁ y₁ h hY hee' hcut N₁ N₂ a1 a2 a5,
        ← ep2_glue_filter α β L X Y e e' x₁ y₁ h hY hee' hcut N₁' N₂' b1 b2 b5, heq]
    have e1 : N₁ = N₁' := by
      rw [← ep2_glue_filter α β L Y X e e' y₁ x₁ h hX hee' hcutY N₂ N₁ a2 a1 a5.symm,
        ← ep2_glue_filter α β L Y X e e' y₁ x₁ h hX hee' hcutY N₂' N₁' b2 b1 b5.symm,
        ← ep2Glue_comm e e' N₁ N₂ a5, ← ep2Glue_comm e e' N₁' N₂' b5, heq]
    rw [e1, e2]
  have hmaps : ∀ p ∈ (↑(P₁ ×ˢ P₂) : Set (Finset E × Finset E)),
      ep2Glue e e' p.1 p.2 ∈ ((epPMs α β L).filter (fun M => g ∈ M) : Finset (Finset E)) := by
    intro p hp
    obtain ⟨a1, a2, a3, a4⟩ := hvalid p (Finset.mem_coe.mp hp)
    rw [Finset.mem_filter, mem_epPMs]
    refine ⟨ep2_glue α β L X Y e e' x₁ y₁ h hb hXL hY hee' hcut p.1 p.2 a1 a2
      ⟨fun _ => a4, fun _ => a3⟩, ?_⟩
    unfold ep2Glue
    rcases hg with rfl | rfl
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ a3)
    · refine Finset.mem_union_right _ ?_
      rw [if_pos a3]; exact Finset.mem_singleton_self _
  have hle := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Finset.card_product] at hle
  unfold epMe
  exact (Nat.mul_le_mul hP₁c hP₂c).trans hle

open Classical in
/-- **Lemma 7(2) for 2-edge-cuts.** If every live edge of the contraction keeping `X` lies in at
least `k₁` perfect matchings and every live edge of the contraction keeping `Y = L \ X` in at
least `k₂`, then every live edge of `G` lies in at least `k₁ k₂` perfect matchings. -/
theorem ep2_mstar {W E : Type*} [Fintype E] (α β : E → W) (L X Y : Finset W) (e e' : E)
    (x₁ y₁ : W) (h : EpCubicD α β L) (hb : EpBridgeless α β L) (hXL : X ⊆ L)
    (hY : ∀ w, w ∈ Y ↔ w ∈ L ∧ w ∉ X) (hx₁ : x₁ ∈ X) (hy₁ : y₁ ∈ Y) (hee' : e ≠ e')
    (hcut : ∀ g, epCross α β X g ↔ g = e ∨ g = e') (k₁ k₂ : ℕ)
    (h₁ : ∀ g, ep2A α β Y e e' y₁ g ∈ L \ Y →
      k₁ ≤ epMe (ep2A α β Y e e' y₁) (ep2B α β Y e e' y₁) (L \ Y) g)
    (h₂ : ∀ g, ep2A α β X e e' x₁ g ∈ L \ X →
      k₂ ≤ epMe (ep2A α β X e e' x₁) (ep2B α β X e e' x₁) (L \ X) g)
    (g : E) (hg : α g ∈ L) : k₁ * k₂ ≤ epMe α β L g := by
  have hYL : Y ⊆ L := fun w hw => ((hY w).mp hw).1
  have hX : ∀ w, w ∈ X ↔ w ∈ L ∧ w ∉ Y := by
    intro w
    constructor
    · intro hw; exact ⟨hXL hw, fun h' => ((hY w).mp h').2 hw⟩
    · rintro ⟨h1, h2⟩; by_contra h'; exact h2 ((hY w).mpr ⟨h1, h'⟩)
  have hcutY := ep2_cut_compl α β L X Y e e' h hY hcut
  have hliveX : ep2A α β X e e' x₁ e ∈ L \ X := by
    obtain ⟨a1, a2, -, -⟩ := ep_cut_insert_card α β L X h hb hXL e e' hee' hcut e (Or.inl rfl)
    have : ep2A α β X e e' x₁ e = epOut α β X e := by unfold ep2A; rw [if_pos rfl]
    rw [this]; exact Finset.mem_sdiff.mpr ⟨a1, a2⟩
  have hliveY : ep2A α β Y e e' y₁ e ∈ L \ Y := by
    obtain ⟨a1, a2, -, -⟩ := ep_cut_insert_card α β L Y h hb hYL e e' hee' hcutY e (Or.inl rfl)
    have : ep2A α β Y e e' y₁ e = epOut α β Y e := by unfold ep2A; rw [if_pos rfl]
    rw [this]; exact Finset.mem_sdiff.mpr ⟨a1, a2⟩
  by_cases hgc : epCross α β X g
  · exact ep2_count_cross α β L X Y e e' x₁ y₁ h hb hXL hY hee' hcut k₁ k₂ (h₁ e hliveY)
      (h₂ e hliveX) g ((hcut g).mp hgc)
  · have hge : g ≠ e := fun h' => hgc ((hcut g).mpr (Or.inl h'))
    have hge' : g ≠ e' := fun h' => hgc ((hcut g).mpr (Or.inr h'))
    have hβ : β g ∈ L := by
      rcases h.1 g with h' | h'
      · exact h'.2.1
      · exact absurd hg h'.1
    by_cases hgX : α g ∈ X
    · -- both ends in `X`
      have hβX : β g ∈ X := by
        by_contra h'; exact hgc (Or.inl ⟨hgX, h'⟩)
      have hlive : ep2A α β Y e e' y₁ g ∈ L \ Y := by
        have hnin : ¬(g = e' ∨ (α g ∈ Y ∧ β g ∈ Y)) := by
          rintro (h' | ⟨h', -⟩)
          · exact hge' h'
          · exact ((hY _).mp h').2 hgX
        unfold ep2A
        rw [if_neg hge, if_neg hnin]
        exact Finset.mem_sdiff.mpr ⟨hg, fun h' => ((hY _).mp h').2 hgX⟩
      have := ep2_count_side α β L Y X e e' y₁ x₁ h hb hYL hX hx₁ hee' hcutY k₂ k₁ h₂ g
        (h₁ g hlive)
      rwa [mul_comm] at this
    · have hβX : β g ∉ X := fun h' => hgc (Or.inr ⟨hgX, h'⟩)
      have hlive : ep2A α β X e e' x₁ g ∈ L \ X := by
        have hnin : ¬(g = e' ∨ (α g ∈ X ∧ β g ∈ X)) := by
          rintro (h' | ⟨h', -⟩)
          · exact hge' h'
          · exact hgX h'
        unfold ep2A
        rw [if_neg hge, if_neg hnin]
        exact Finset.mem_sdiff.mpr ⟨hg, hgX⟩
      exact ep2_count_side α β L X Y e e' x₁ y₁ h hb hXL hY hy₁ hee' hcut k₁ k₂ h₁ g
        (h₂ g hlive)

lemma epD_cross_compl {W E : Type*} [Fintype E] (α β : E → W) (L X Y : Finset W)
    (h : EpCubicD α β L) (hY : ∀ w, w ∈ Y ↔ w ∈ L ∧ w ∉ X) (g : E) :
    epCross α β Y g ↔ epCross α β X g := by
  by_cases hg : α g = β g
  · have h1 : ¬epCross α β Y g := by unfold epCross; rw [hg]; tauto
    have h2 : ¬epCross α β X g := by unfold epCross; rw [hg]; tauto
    exact iff_of_false h1 h2
  · have hl : α g ∈ L ∧ β g ∈ L := by
      rcases h.1 g with h' | h'
      · exact ⟨h'.1, h'.2.1⟩
      · exact absurd h'.2.symm hg
    unfold epCross
    simp only [hY, hl.1, hl.2, true_and]
    tauto

/-- Edges of a perfect matching of the contraction of `X` are not loops and not inside `X`. -/
lemma epCon_pm_edge {W E : Type*} (α β : E → W) (L' X : Finset W) (x₀ x₁ : W)
    {N : Finset E} (hN : N ∈ epPM (epConA α β X x₀ x₁) (epConB α β X x₀ x₁) L') (g : E)
    (hg : g ∈ N) : α g ≠ β g ∧ ¬(α g ∈ X ∧ β g ∈ X) := by
  classical
  have hnl := hN.1 g hg
  have hA : epConA α β X x₀ x₁ g = if α g ∈ X ∧ β g ∈ X then x₁ else epRho X x₀ (α g) := rfl
  have hB : epConB α β X x₀ x₁ g = if α g ∈ X ∧ β g ∈ X then x₁ else epRho X x₀ (β g) := rfl
  rw [hA, hB] at hnl
  by_cases hin : α g ∈ X ∧ β g ∈ X
  · rw [if_pos hin, if_pos hin] at hnl; exact absurd rfl hnl
  · rw [if_neg hin, if_neg hin] at hnl
    exact ⟨fun h' => hnl (by rw [h']), hin⟩

lemma epCon_pm_cut {W E : Type*} (α β : E → W) (L X : Finset W) (x₀ x₁ : W) (hx₀ : x₀ ∈ X)
    {N : Finset E} (hN : N ∈ epPM (epConA α β X x₀ x₁) (epConB α β X x₀ x₁) (epL' L X x₀)) :
    ∃! f, f ∈ N ∧ epCross α β X f := by
  classical
  have hmem : x₀ ∈ epL' L X x₀ := by unfold epL'; exact Finset.mem_insert_self _ _
  have h := hN.2 x₀ hmem
  simpa only [epCon_cross α β L X x₀ x₁ hx₀ {x₀} (Finset.singleton_subset_iff.mpr hmem),
    epLift_singleton_t₀ X x₀ hx₀] using h

lemma epCon_pm_vertex {W E : Type*} (α β : E → W) (L X : Finset W) (x₀ x₁ : W) (hx₀ : x₀ ∈ X)
    {N : Finset E} (hN : N ∈ epPM (epConA α β X x₀ x₁) (epConB α β X x₀ x₁) (epL' L X x₀))
    (c : W) (hc : c ∈ L) (hcX : c ∉ X) : ∃! g, g ∈ N ∧ epCross α β {c} g := by
  classical
  have hc' : c ∈ epL' L X x₀ := by
    unfold epL'; exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨hc, hcX⟩)
  have h := hN.2 c hc'
  have hne : c ≠ x₀ := fun h' => hcX (h' ▸ hx₀)
  simpa only [epCon_cross α β L X x₀ x₁ hx₀ {c} (Finset.singleton_subset_iff.mpr hc'),
    epLift_singleton_ne X x₀ c hne] using h

lemma epCon_pm_touch {W E : Type*} (α β : E → W) (L' X : Finset W) (x₀ x₁ : W)
    {N : Finset E} (hN : N ∈ epPM (epConA α β X x₀ x₁) (epConB α β X x₀ x₁) L') {g : E}
    (hg : g ∈ N) (c : W) (hc : c ∈ X) (hcross : epCross α β {c} g) : epCross α β X g := by
  have h := (epCon_pm_edge α β L' X x₀ x₁ hN g hg).2
  rw [epCross_singleton] at hcross
  unfold epCross
  rcases hcross with ⟨h1, -⟩ | ⟨-, h2⟩
  · left; exact ⟨h1 ▸ hc, fun hb => h ⟨h1 ▸ hc, hb⟩⟩
  · right; exact ⟨fun ha => h ⟨ha, h2 ▸ hc⟩, h2 ▸ hc⟩

open Classical in
/-- **Matching correspondence for 3-cut contraction (gluing direction).** -/
lemma ep3_glue {W E : Type*} [Fintype E] (α β : E → W) (L X Y : Finset W) (x₀ x₁ y₀ y₁ : W)
    (h : EpCubicD α β L) (hY : ∀ w, w ∈ Y ↔ w ∈ L ∧ w ∉ X) (hx₀ : x₀ ∈ X) (hy₀ : y₀ ∈ Y)
    {N₁ N₂ : Finset E}
    (hN₁ : N₁ ∈ epPM (epConA α β Y y₀ y₁) (epConB α β Y y₀ y₁) (epL' L Y y₀))
    (hN₂ : N₂ ∈ epPM (epConA α β X x₀ x₁) (epConB α β X x₀ x₁) (epL' L X x₀))
    (f : E) (hf₁ : f ∈ N₁) (hf₂ : f ∈ N₂) (hfc : epCross α β X f) :
    N₁ ∪ N₂ ∈ epPM α β L := by
  have hcut₁ := epCon_pm_cut α β L Y y₀ y₁ hy₀ hN₁
  simp only [epD_cross_compl α β L X Y h hY] at hcut₁
  have hcut₂ := epCon_pm_cut α β L X x₀ x₁ hx₀ hN₂
  refine ⟨fun g hg => ?_, fun c hc => ?_⟩
  · rcases Finset.mem_union.mp hg with h' | h'
    · exact (epCon_pm_edge α β _ Y y₀ y₁ hN₁ g h').1
    · exact (epCon_pm_edge α β _ X x₀ x₁ hN₂ g h').1
  · by_cases hcX : c ∈ X
    · -- `c ∈ X`: its matching edge comes from `N₁`
      have hcY : c ∉ Y := fun h' => ((hY c).mp h').2 hcX
      refine ep_glue_unique _ N₁ N₂ f hf₁ (epCon_pm_vertex α β L Y y₀ y₁ hy₀ hN₁ c hc hcY) ?_
      intro g hg hcross
      have h1 := epCon_pm_touch α β _ X x₀ x₁ hN₂ hg c hcX hcross
      exact hcut₂.unique ⟨hg, h1⟩ ⟨hf₂, hfc⟩
    · have hcY : c ∈ Y := (hY c).mpr ⟨hc, hcX⟩
      rw [Finset.union_comm]
      refine ep_glue_unique _ N₂ N₁ f hf₂ (epCon_pm_vertex α β L X x₀ x₁ hx₀ hN₂ c hc hcX) ?_
      intro g hg hcross
      have h1 := epCon_pm_touch α β _ Y y₀ y₁ hN₁ hg c hcY hcross
      rw [epD_cross_compl α β L X Y h hY] at h1
      exact hcut₁.unique ⟨hg, h1⟩ ⟨hf₁, hfc⟩

open Classical in
/-- The glued matching determines the matching of the contraction of `X`. -/
lemma ep3_glue_filter {W E : Type*} [Fintype E] (α β : E → W) (L X Y : Finset W)
    (x₀ x₁ y₀ y₁ : W) (h : EpCubicD α β L) (hY : ∀ w, w ∈ Y ↔ w ∈ L ∧ w ∉ X) (hy₀ : y₀ ∈ Y)
    {N₁ N₂ : Finset E}
    (hN₁ : N₁ ∈ epPM (epConA α β Y y₀ y₁) (epConB α β Y y₀ y₁) (epL' L Y y₀))
    (hN₂ : N₂ ∈ epPM (epConA α β X x₀ x₁) (epConB α β X x₀ x₁) (epL' L X x₀))
    (f : E) (hf₁ : f ∈ N₁) (hf₂ : f ∈ N₂) (hfc : epCross α β X f) :
    (N₁ ∪ N₂).filter (fun g => ¬(α g ∈ X ∧ β g ∈ X)) = N₂ := by
  have hcut₁ := epCon_pm_cut α β L Y y₀ y₁ hy₀ hN₁
  simp only [epD_cross_compl α β L X Y h hY] at hcut₁
  ext g
  rw [Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨hg | hg, hnot⟩
    · have a := epCon_pm_edge α β _ Y y₀ y₁ hN₁ g hg
      have hl : α g ∈ L ∧ β g ∈ L := by
        rcases h.1 g with h' | h'
        · exact ⟨h'.1, h'.2.1⟩
        · exact absurd h'.2.symm a.1
      have b1 := hY (α g); have b2 := hY (β g)
      have hc : epCross α β X g := by unfold epCross; tauto
      exact (hcut₁.unique ⟨hg, hc⟩ ⟨hf₁, hfc⟩) ▸ hf₂
    · exact hg
  · intro hg
    exact ⟨Or.inr hg, (epCon_pm_edge α β _ X x₀ x₁ hN₂ g hg).2⟩

set_option maxHeartbeats 1600000 in
open Classical in
/-- **Lemma 7(2) for cut contractions, one side.** -/
lemma ep3_count_side {W E : Type*} [Fintype E] (α β : E → W) (L X Y : Finset W)
    (x₀ x₁ y₀ y₁ : W) (h : EpCubicD α β L) (hXL : X ⊆ L)
    (hY : ∀ w, w ∈ Y ↔ w ∈ L ∧ w ∉ X) (hx₀ : x₀ ∈ X) (hy₀ : y₀ ∈ Y) (k₁ k₂ : ℕ)
    (h₁ : ∀ g, epConA α β Y y₀ y₁ g ∈ epL' L Y y₀ →
      k₁ ≤ epMe (epConA α β Y y₀ y₁) (epConB α β Y y₀ y₁) (epL' L Y y₀) g)
    (g : E) (h₂ : k₂ ≤ epMe (epConA α β X x₀ x₁) (epConB α β X x₀ x₁) (epL' L X x₀) g) :
    k₁ * k₂ ≤ epMe α β L g := by
  have hX : ∀ w, w ∈ X ↔ w ∈ L ∧ w ∉ Y := by
    intro w
    constructor
    · intro hw; exact ⟨hXL hw, fun h' => ((hY w).mp h').2 hw⟩
    · rintro ⟨h1, h2⟩; by_contra h'; exact h2 ((hY w).mpr ⟨h1, h'⟩)
  obtain ⟨S₂, hS₂⟩ : ∃ P : Finset (Finset E), P =
      (epPMs (epConA α β X x₀ x₁) (epConB α β X x₀ x₁) (epL' L X x₀)).filter
        (fun N => g ∈ N) := ⟨_, rfl⟩
  have hS₂c : k₂ ≤ S₂.card := by rw [hS₂]; exact h₂
  have hS₂m : ∀ N, N ∈ S₂ →
      N ∈ epPM (epConA α β X x₀ x₁) (epConB α β X x₀ x₁) (epL' L X x₀) ∧ g ∈ N := by
    intro N hN; rw [hS₂, Finset.mem_filter, mem_epPMs] at hN; exact hN
  obtain ⟨B, hB⟩ : ∃ B : Finset E → Finset (Finset E), B = fun N₂ =>
      (epPMs (epConA α β Y y₀ y₁) (epConB α β Y y₀ y₁) (epL' L Y y₀)).filter
        (fun N₁ => ∃ f, f ∈ N₂ ∧ f ∈ N₁ ∧ epCross α β X f) := ⟨_, rfl⟩
  have hBm : ∀ N₂ N₁, N₁ ∈ B N₂ →
      N₁ ∈ epPM (epConA α β Y y₀ y₁) (epConB α β Y y₀ y₁) (epL' L Y y₀) ∧
        ∃ f, f ∈ N₂ ∧ f ∈ N₁ ∧ epCross α β X f := by
    intro N₂ N₁ hN; rw [hB, Finset.mem_filter, mem_epPMs] at hN; exact hN
  have hBc : ∀ N₂ ∈ S₂, k₁ ≤ (B N₂).card := by
    intro N₂ hN₂
    obtain ⟨f₀, ⟨hf1, hf2⟩, -⟩ := epCon_pm_cut α β L X x₀ x₁ hx₀ (hS₂m N₂ hN₂).1
    have hlive := epD_live_of_cross h X f₀ hf2
    have hfY : ¬(α f₀ ∈ Y ∧ β f₀ ∈ Y) := by
      have := (epD_cross_compl α β L X Y h hY f₀).mpr hf2
      unfold epCross at this; tauto
    have hl₁ : epConA α β Y y₀ y₁ f₀ ∈ epL' L Y y₀ := by
      unfold epConA; rw [if_neg hfY]; exact epRho_mem_L' L Y y₀ _ hlive.1
    refine (h₁ f₀ hl₁).trans (Finset.card_le_card ?_)
    intro N₁ hN₁
    rw [Finset.mem_filter] at hN₁
    rw [hB, Finset.mem_filter]
    exact ⟨hN₁.1, f₀, hf1, hN₁.2, hf2⟩
  have hinj : Set.InjOn (fun p : (_ : Finset E) × Finset E => p.2 ∪ p.1) ↑(S₂.sigma B) := by
    rintro ⟨N₂, N₁⟩ hp ⟨N₂', N₁'⟩ hp' heq
    rw [Finset.mem_coe, Finset.mem_sigma] at hp hp'
    obtain ⟨a1, f, hf2, hf1, hfc⟩ := hBm _ _ hp.2
    obtain ⟨b1, f', hf2', hf1', hfc'⟩ := hBm _ _ hp'.2
    have a2 := (hS₂m _ hp.1).1
    have b2 := (hS₂m _ hp'.1).1
    dsimp only at heq a1 a2 b1 b2 hf1 hf2 hf1' hf2'
    have e2 : N₂ = N₂' := by
      rw [← ep3_glue_filter α β L X Y x₀ x₁ y₀ y₁ h hY hy₀ a1 a2 f hf1 hf2 hfc,
        ← ep3_glue_filter α β L X Y x₀ x₁ y₀ y₁ h hY hy₀ b1 b2 f' hf1' hf2' hfc', heq]
    have hfcY := (epD_cross_compl α β L X Y h hY f).mpr hfc
    have hfcY' := (epD_cross_compl α β L X Y h hY f').mpr hfc'
    have e1 : N₁ = N₁' := by
      rw [← ep3_glue_filter α β L Y X y₀ y₁ x₀ x₁ h hX hx₀ a2 a1 f hf2 hf1 hfcY,
        ← ep3_glue_filter α β L Y X y₀ y₁ x₀ x₁ h hX hx₀ b2 b1 f' hf2' hf1' hfcY',
        Finset.union_comm N₂ N₁, Finset.union_comm N₂' N₁', heq]
    rw [e1, e2]
  have hmaps : ∀ p ∈ (↑(S₂.sigma B) : Set ((_ : Finset E) × Finset E)),
      p.2 ∪ p.1 ∈ ((epPMs α β L).filter (fun M => g ∈ M) : Finset (Finset E)) := by
    intro p hp
    rw [Finset.mem_coe, Finset.mem_sigma] at hp
    obtain ⟨a1, f, hf2, hf1, hfc⟩ := hBm _ _ hp.2
    have a2 := hS₂m _ hp.1
    rw [Finset.mem_filter, mem_epPMs]
    exact ⟨ep3_glue α β L X Y x₀ x₁ y₀ y₁ h hY hx₀ hy₀ a1 a2.1 f hf1 hf2 hfc,
      Finset.mem_union_right _ a2.2⟩
  have hle := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Finset.card_sigma] at hle
  have hsum : S₂.card • k₁ ≤ ∑ N₂ ∈ S₂, (B N₂).card :=
    Finset.card_nsmul_le_sum _ _ _ hBc
  rw [smul_eq_mul] at hsum
  unfold epMe
  calc k₁ * k₂ ≤ S₂.card * k₁ := by rw [mul_comm]; exact Nat.mul_le_mul_right _ hS₂c
    _ ≤ _ := hsum.trans hle

open Classical in
/-- **Lemma 7(2) for cut contractions to a vertex** (in particular 3-edge-cuts). If every live
edge of the contraction of `Y = L \ X` lies in at least `k₁` perfect matchings and every live
edge of the contraction of `X` in at least `k₂`, then every live edge of `G` lies in at least
`k₁ k₂` perfect matchings. -/
theorem ep3_mstar {W E : Type*} [Fintype E] (α β : E → W) (L X Y : Finset W)
    (x₀ x₁ y₀ y₁ : W) (h : EpCubicD α β L) (hXL : X ⊆ L)
    (hY : ∀ w, w ∈ Y ↔ w ∈ L ∧ w ∉ X) (hx₀ : x₀ ∈ X) (hy₀ : y₀ ∈ Y) (k₁ k₂ : ℕ)
    (h₁ : ∀ g, epConA α β Y y₀ y₁ g ∈ epL' L Y y₀ →
      k₁ ≤ epMe (epConA α β Y y₀ y₁) (epConB α β Y y₀ y₁) (epL' L Y y₀) g)
    (h₂ : ∀ g, epConA α β X x₀ x₁ g ∈ epL' L X x₀ →
      k₂ ≤ epMe (epConA α β X x₀ x₁) (epConB α β X x₀ x₁) (epL' L X x₀) g)
    (g : E) (hg : α g ∈ L) : k₁ * k₂ ≤ epMe α β L g := by
  have hYL : Y ⊆ L := fun w hw => ((hY w).mp hw).1
  have hX : ∀ w, w ∈ X ↔ w ∈ L ∧ w ∉ Y := by
    intro w
    constructor
    · intro hw; exact ⟨hXL hw, fun h' => ((hY w).mp h').2 hw⟩
    · rintro ⟨h1, h2⟩; by_contra h'; exact h2 ((hY w).mpr ⟨h1, h'⟩)
  by_cases hin : α g ∈ X ∧ β g ∈ X
  · -- inside `X`: live in the contraction of `Y`
    have hnY : ¬(α g ∈ Y ∧ β g ∈ Y) := fun h' => ((hY _).mp h'.1).2 hin.1
    have hl : epConA α β Y y₀ y₁ g ∈ epL' L Y y₀ := by
      unfold epConA; rw [if_neg hnY]; exact epRho_mem_L' L Y y₀ _ hg
    have := ep3_count_side α β L Y X y₀ y₁ x₀ x₁ h hYL hX hy₀ hx₀ k₂ k₁ h₂ g (h₁ g hl)
    rwa [mul_comm] at this
  · have hl : epConA α β X x₀ x₁ g ∈ epL' L X x₀ := by
      unfold epConA; rw [if_neg hin]; exact epRho_mem_L' L X x₀ _ hg
    exact ep3_count_side α β L X Y x₀ x₁ y₀ y₁ h hXL hY hx₀ hy₀ k₁ k₂ h₁ g (h₂ g hl)

/-- Version of `epAlt_le_altNum` for multigraphs with dead edges: no loops at vertices of `X`. -/
lemma epAlt_le_altNum' {W E : Type*} [Fintype E] (α β : E → W) (X : Finset W)
    (hnl : ∀ e, α e ∈ X → α e ≠ β e) (M : Finset E) (k : ℕ) (h : EpAlt α β X M k) :
    k ≤ epAltNum α β X M := by
  classical
  have hk : k ≤ Fintype.card E := by
    obtain ⟨D, hne, hin, -, hdisj⟩ := h
    choose g hg using hne
    have hinj : Function.Injective g := by
      intro i j hij
      by_contra hne'
      have hcr : epCross α β {α (g i)} (g i) :=
        (ep_cross_ends α β (g i) (hnl _ (hin i _ (hg i)).1) _).mpr (Or.inl rfl)
      exact hdisj i j hne' (α (g i)) ⟨⟨g i, hg i, hcr⟩, ⟨g i, hij ▸ hg j, hcr⟩⟩
    simpa using Fintype.card_le_of_injective g hinj
  unfold epAltNum
  exact Nat.le_findGreatest hk h

set_option maxHeartbeats 1600000 in
open Classical in
/-- **Locality of burls.** If, up to a relabelling `σ` of the edges, two multigraphs look the same
from the vertex set `Z` (same incidences with vertices of `Z`, same edges of `E_Z`, same edges
inside `Z`), then a burl of the second is a burl of the first. -/
theorem ep_burl_transfer {W E : Type*} [Fintype E] (α β α' β' : E → W) (Z : Finset W)
    (σ : E ≃ E) (hnl : ∀ e, α e ∈ Z → α e ≠ β e)
    (hcr : ∀ g c, c ∈ Z → (epCross α' β' {c} (σ g) ↔ epCross α β {c} g))
    (hEZ : ∀ g, (α' (σ g) ∈ Z ∨ β' (σ g) ∈ Z) ↔ (α g ∈ Z ∨ β g ∈ Z))
    (hin : ∀ g, (α' (σ g) ∈ Z ∧ β' (σ g) ∈ Z) ↔ (α g ∈ Z ∧ β g ∈ Z))
    (hburl : EpBurl α' β' Z) : EpBurl α β Z := by
  -- local matchings correspond
  have hLM : ∀ N : Finset E, N ∈ epLM α β Z → N.map σ.toEmbedding ∈ epLM α' β' Z := by
    intro N hN
    refine ⟨fun g' hg' => ?_, fun c hc => ?_⟩
    · obtain ⟨g, hg, rfl⟩ := Finset.mem_map.mp hg'
      exact (hEZ g).mpr (hN.1 g hg)
    · obtain ⟨g, ⟨h1, h2⟩, huniq⟩ := hN.2 c hc
      refine ⟨σ g, ⟨Finset.mem_map.mpr ⟨g, h1, rfl⟩, (hcr g c hc).mpr h2⟩, ?_⟩
      rintro g' ⟨hg', hc'⟩
      obtain ⟨g₂, hg₂, rfl⟩ := Finset.mem_map.mp hg'
      have := huniq g₂ ⟨hg₂, (hcr g₂ c hc).mp hc'⟩
      exact congrArg σ this
  have hLM' : ∀ N : Finset E, N.map σ.toEmbedding ∈ epLM α' β' Z → N ∈ epLM α β Z := by
    intro N hN
    refine ⟨fun g hg => ?_, fun c hc => ?_⟩
    · exact (hEZ g).mp (hN.1 (σ g) (Finset.mem_map.mpr ⟨g, hg, rfl⟩))
    · obtain ⟨g', ⟨h1, h2⟩, huniq⟩ := hN.2 c hc
      obtain ⟨g, hg, rfl⟩ := Finset.mem_map.mp h1
      refine ⟨g, ⟨hg, (hcr g c hc).mp h2⟩, ?_⟩
      rintro g₂ ⟨hg₂, hc₂⟩
      have := huniq (σ g₂) ⟨Finset.mem_map.mpr ⟨g₂, hg₂, rfl⟩, (hcr g₂ c hc).mpr hc₂⟩
      exact σ.injective this
  -- alternating families pull back
  have hAlt : ∀ (N : Finset E) (k : ℕ), EpAlt α' β' Z (N.map σ.toEmbedding) k →
      EpAlt α β Z N k := by
    rintro N k ⟨D', hne, hins, hflip, hdisj⟩
    refine ⟨fun i => (D' i).map σ.symm.toEmbedding, fun i => ?_, fun i g hg => ?_, fun i => ?_,
      fun i j hij c => ?_⟩
    · obtain ⟨g, hg⟩ := hne i
      exact ⟨σ.symm g, Finset.mem_map.mpr ⟨g, hg, rfl⟩⟩
    · obtain ⟨g', hg', rfl⟩ := Finset.mem_map.mp hg
      have := hins i g' hg'
      refine (hin (σ.symm g')).mp ?_
      simpa using this
    · apply hLM'
      have hmap : (symmDiff N ((D' i).map σ.symm.toEmbedding)).map σ.toEmbedding =
          symmDiff (N.map σ.toEmbedding) (D' i) := by
        ext g'
        simp only [Finset.mem_map, Finset.mem_symmDiff, Equiv.coe_toEmbedding]
        constructor
        · rintro ⟨g, (⟨h1, h2⟩ | ⟨h1, h2⟩), rfl⟩
          · exact Or.inl ⟨⟨g, h1, rfl⟩, fun h' => h2 ⟨σ g, h', by simp⟩⟩
          · obtain ⟨g₂, hg₂, rfl⟩ := h1
            refine Or.inr ⟨by simpa using hg₂, ?_⟩
            rintro ⟨g₃, hg₃, h3⟩
            have : g₃ = σ.symm g₂ := σ.injective h3
            exact h2 (this ▸ hg₃)
        · rintro (⟨⟨g, h1, rfl⟩, h2⟩ | ⟨h1, h2⟩)
          · exact ⟨g, Or.inl ⟨h1, fun ⟨g₂, hg₂, h3⟩ => h2 (by
              have : σ g = g₂ := by rw [← h3]; simp
              exact this ▸ hg₂)⟩, rfl⟩
          · exact ⟨σ.symm g', Or.inr ⟨⟨g', h1, rfl⟩, fun h' => h2 ⟨σ.symm g', h', by simp⟩⟩,
              by simp⟩
      rw [hmap]; exact hflip i
    · rintro ⟨⟨g, hg, hgc⟩, ⟨g₂, hg₂, hg₂c⟩⟩
      obtain ⟨g', hg', rfl⟩ := Finset.mem_map.mp hg
      obtain ⟨g₂', hg₂', rfl⟩ := Finset.mem_map.mp hg₂
      -- the vertex `c` lies in `Z`, since the edges are inside `Z`
      have hcZ : c ∈ Z := by
        have h1 := (hin (σ.symm g')).mp (by simpa using hins i g' hg')
        rw [epCross_singleton] at hgc
        rcases hgc with ⟨h', -⟩ | ⟨-, h'⟩
        · exact h' ▸ h1.1
        · exact h' ▸ h1.2
      apply hdisj i j hij c
      refine ⟨⟨g', hg', ?_⟩, ⟨g₂', hg₂', ?_⟩⟩
      · have := (hcr (σ.symm g') c hcZ).mpr hgc
        simpa using this
      · have := (hcr (σ.symm g₂') c hcZ).mpr hg₂c
        simpa using this
  have hnum : ∀ N : Finset E, epAltNum α' β' Z (N.map σ.toEmbedding) ≤ epAltNum α β Z N :=
    fun N => epAlt_le_altNum' α β Z hnl N _ (hAlt N _ (epAltNum_spec α' β' Z _))
  intro p hp
  obtain ⟨hp0, hpS, hp1, hpb⟩ := hp
  -- the transported distribution
  have hsumeq : ∀ f : Finset E → ℝ,
      ∑ N' : Finset E, p (N'.map σ.symm.toEmbedding) * f N' =
        ∑ N : Finset E, p N * f (N.map σ.toEmbedding) := by
    intro f
    refine Fintype.sum_equiv (Equiv.finsetCongr σ.symm) _ _ (fun N' => ?_)
    have h1 : (Equiv.finsetCongr σ.symm) N' = N'.map σ.symm.toEmbedding := rfl
    rw [h1]
    congr 2
    ext g
    simp [Finset.mem_map]
  have hbal : EpBalanced α' β' Z (fun N' => p (N'.map σ.symm.toEmbedding)) := by
    refine ⟨fun N' => hp0 _, fun N' hN' => ?_, ?_, fun g' hg' => ?_⟩
    · have := hLM _ (hpS _ hN')
      have h2 : (N'.map σ.symm.toEmbedding).map σ.toEmbedding = N' := by
        ext g; simp [Finset.mem_map]
      rwa [h2] at this
    · have := hsumeq (fun _ => 1)
      simp only [mul_one] at this
      rw [this]; exact hp1
    · rw [hsumeq (fun N' => epInd N' g')]
      have hg : α (σ.symm g') ∈ Z ∨ β (σ.symm g') ∈ Z := by
        refine (hEZ (σ.symm g')).mp ?_
        simpa using hg'
      rw [← hpb (σ.symm g') hg]
      refine Finset.sum_congr rfl fun N _ => ?_
      congr 1
      unfold epInd
      have : g' ∈ N.map σ.toEmbedding ↔ σ.symm g' ∈ N := by
        simp only [Finset.mem_map, Equiv.coe_toEmbedding]
        constructor
        · rintro ⟨g₀, hgN, rfl⟩; rw [Equiv.symm_apply_apply]; exact hgN
        · intro h'; exact ⟨σ.symm g', h', by simp⟩
      simp only [this]
  have h3 := hburl _ hbal
  rw [hsumeq (fun N' => (epAltNum α' β' Z N' : ℝ))] at h3
  refine h3.trans (Finset.sum_le_sum fun N _ => ?_)
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hnum N) (hp0 N)

/-- Under the hypotheses of `ep_burl_transfer` the cut of `Z` has the same size. -/
lemma ep_cut_card_transfer {W E : Type*} [Fintype E] (α β α' β' : E → W) (Z : Finset W)
    (σ : E ≃ E)
    (hEZ : ∀ g, (α' (σ g) ∈ Z ∨ β' (σ g) ∈ Z) ↔ (α g ∈ Z ∨ β g ∈ Z))
    (hin : ∀ g, (α' (σ g) ∈ Z ∧ β' (σ g) ∈ Z) ↔ (α g ∈ Z ∧ β g ∈ Z)) :
    (epCut α β Z).card = (epCut α' β' Z).card := by
  classical
  refine Finset.card_bij (fun g _ => σ g) (fun g hg => ?_) (fun a _ b _ h => σ.injective h)
    (fun g' hg' => ?_)
  · rw [mem_epCut] at hg ⊢
    have h1 := hEZ g; have h2 := hin g
    unfold epCross at hg ⊢
    tauto
  · refine ⟨σ.symm g', ?_, by simp⟩
    rw [mem_epCut] at hg' ⊢
    have h1 := hEZ (σ.symm g'); have h2 := hin (σ.symm g')
    rw [Equiv.apply_symm_apply] at h1 h2
    unfold epCross at hg' ⊢
    tauto

/-- **Lemma 7(3) for contraction to a vertex** (3-edge-cuts): a burl of the contraction that
avoids the contracted set is a burl of `G`, and its cut has the same size. -/
theorem epCon_burl {W E : Type*} [Fintype E] (α β : E → W) (L X Z : Finset W) (x₀ x₁ : W)
    (h : EpCubicD α β L) (hXL : X ⊆ L) (hx₀ : x₀ ∈ X) (hx₁ : x₁ ∈ X) (hZL : Z ⊆ L)
    (hZX : ∀ w, w ∈ Z → w ∉ X)
    (hburl : EpBurl (epConA α β X x₀ x₁) (epConB α β X x₀ x₁) Z) :
    EpBurl α β Z ∧
      (epCut α β Z).card = (epCut (epConA α β X x₀ x₁) (epConB α β X x₀ x₁) Z).card := by
  classical
  have hx₀Z : x₀ ∉ Z := fun h' => hZX _ h' hx₀
  have hx₁Z : x₁ ∉ Z := fun h' => hZX _ h' hx₁
  have hρ : ∀ w, epRho X x₀ w ∈ Z ↔ w ∈ Z := by
    intro w
    unfold epRho
    by_cases hw : w ∈ X
    · rw [if_pos hw]; exact iff_of_false hx₀Z (fun h' => hZX _ h' hw)
    · rw [if_neg hw]
  have hA : ∀ g, epConA α β X x₀ x₁ g ∈ Z ↔ α g ∈ Z := by
    intro g
    unfold epConA
    by_cases hin : α g ∈ X ∧ β g ∈ X
    · rw [if_pos hin]; exact iff_of_false hx₁Z (fun h' => hZX _ h' hin.1)
    · rw [if_neg hin]; exact hρ _
  have hB : ∀ g, epConB α β X x₀ x₁ g ∈ Z ↔ β g ∈ Z := by
    intro g
    unfold epConB
    by_cases hin : α g ∈ X ∧ β g ∈ X
    · rw [if_pos hin]; exact iff_of_false hx₁Z (fun h' => hZX _ h' hin.2)
    · rw [if_neg hin]; exact hρ _
  have hEZ : ∀ g, (epConA α β X x₀ x₁ ((Equiv.refl E) g) ∈ Z ∨
      epConB α β X x₀ x₁ ((Equiv.refl E) g) ∈ Z) ↔ (α g ∈ Z ∨ β g ∈ Z) := by
    intro g; rw [Equiv.refl_apply, hA, hB]
  have hin : ∀ g, (epConA α β X x₀ x₁ ((Equiv.refl E) g) ∈ Z ∧
      epConB α β X x₀ x₁ ((Equiv.refl E) g) ∈ Z) ↔ (α g ∈ Z ∧ β g ∈ Z) := by
    intro g; rw [Equiv.refl_apply, hA, hB]
  refine ⟨ep_burl_transfer α β _ _ Z (Equiv.refl E) ?_ ?_ hEZ hin hburl,
    ep_cut_card_transfer α β _ _ Z (Equiv.refl E) hEZ hin⟩
  · intro e he
    rcases h.1 e with h' | h'
    · exact h'.2.2
    · exact absurd (hZL he) h'.1
  · intro g c hc
    rw [Equiv.refl_apply]
    have hcX : c ∉ X := hZX c hc
    have hc' : c ∈ epL' L X x₀ := by
      unfold epL'; exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨hZL hc, hcX⟩)
    rw [epCon_cross α β L X x₀ x₁ hx₀ {c} (Finset.singleton_subset_iff.mpr hc'),
      epLift_singleton_ne X x₀ c (fun h' => hcX (h' ▸ hx₀))]

/-- The edge `g'` of `(α', β')` looks from `Z` like the edge `g` of `(α, β)`. -/
def epSame {W E : Type*} (α β α' β' : E → W) (Z : Finset W) (g' g : E) : Prop :=
  (∀ c ∈ Z, epCross α' β' {c} g' ↔ epCross α β {c} g) ∧
    ((α' g' ∈ Z ∨ β' g' ∈ Z) ↔ (α g ∈ Z ∨ β g ∈ Z)) ∧
    ((α' g' ∈ Z ∧ β' g' ∈ Z) ↔ (α g ∈ Z ∧ β g ∈ Z))

set_option maxHeartbeats 1600000 in
/-- Two edges whose second ends lie outside `Z` and whose first ends agree, or both lie outside
`Z`, look the same from `Z`. -/
lemma epSame_of_ends {W E : Type*} (α β α' β' : E → W) (Z : Finset W) (g' g : E)
    (p' q' p q : W)
    (h' : (α' g' = p' ∧ β' g' = q') ∨ (α' g' = q' ∧ β' g' = p'))
    (h : (α g = p ∧ β g = q) ∨ (α g = q ∧ β g = p))
    (hq' : q' ∉ Z) (hq : q ∉ Z) (hp : p' = p ∨ (p' ∉ Z ∧ p ∉ Z)) :
    epSame α β α' β' Z g' g := by
  have e1 : (α' g' ∈ Z ∨ β' g' ∈ Z) ↔ p' ∈ Z := by
    rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> tauto
  have e2 : (α g ∈ Z ∨ β g ∈ Z) ↔ p ∈ Z := by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> tauto
  have e3 : ¬(α' g' ∈ Z ∧ β' g' ∈ Z) := by
    rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> tauto
  have e4 : ¬(α g ∈ Z ∧ β g ∈ Z) := by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> tauto
  have e5 : p' ∈ Z ↔ p ∈ Z := by
    rcases hp with rfl | ⟨h1, h2⟩
    · rfl
    · exact iff_of_false h1 h2
  refine ⟨fun c hc => ?_, by rw [e1, e2, e5], iff_of_false e3 e4⟩
  have hq'c : q' ≠ c := fun h1 => hq' (h1 ▸ hc)
  have hqc : q ≠ c := fun h1 => hq (h1 ▸ hc)
  rw [ep_cross_pq α' β' g' p' q' h', ep_cross_pq α β g p q h]
  simp only [Finset.mem_singleton]
  rcases hp with rfl | ⟨h1, h2⟩
  · constructor
    · rintro (⟨h3, -⟩ | ⟨-, h4⟩)
      · exact Or.inl ⟨h3, hqc⟩
      · exact absurd h4 hq'c
    · rintro (⟨h3, -⟩ | ⟨-, h4⟩)
      · exact Or.inl ⟨h3, hq'c⟩
      · exact absurd h4 hqc
  · have a1 : p' ≠ c := fun h3 => h1 (h3 ▸ hc)
    have a2 : p ≠ c := fun h3 => h2 (h3 ▸ hc)
    constructor
    · rintro (⟨h3, -⟩ | ⟨-, h4⟩)
      · exact absurd h3 a1
      · exact absurd h4 hq'c
    · rintro (⟨h3, -⟩ | ⟨-, h4⟩)
      · exact absurd h3 a2
      · exact absurd h4 hqc

lemma epSame_of_eq {W E : Type*} (α β α' β' : E → W) (Z : Finset W) (g : E)
    (hA : α' g = α g) (hB : β' g = β g) : epSame α β α' β' Z g g := by
  refine ⟨fun c _ => ?_, by rw [hA, hB], by rw [hA, hB]⟩
  unfold epCross; rw [hA, hB]

set_option maxHeartbeats 1600000 in
open Classical in
/-- **Lemma 7(3) for 2-edge-cuts.** A burl `Z` of the 2-cut contraction that does not contain
both ends of the new edge is a burl of `G`, and its cut has the same size. -/
theorem ep2_burl {W E : Type*} [Fintype E] (α β : E → W) (L X Z : Finset W) (e e' : E)
    (x₁ : W) (h : EpCubicD α β L) (hx₁ : x₁ ∈ X)
    (hee' : e ≠ e') (hcut : ∀ g, epCross α β X g ↔ g = e ∨ g = e') (hZL : Z ⊆ L)
    (hZX : ∀ w, w ∈ Z → w ∉ X)
    (hnew : ¬(epOut α β X e ∈ Z ∧ epOut α β X e' ∈ Z))
    (hburl : EpBurl (ep2A α β X e e' x₁) (ep2B α β X e e' x₁) Z) :
    EpBurl α β Z ∧
      (epCut α β Z).card = (epCut (ep2A α β X e e' x₁) (ep2B α β X e e' x₁) Z).card := by
  obtain ⟨-, x, hx, hex⟩ := epOut_ends α β X e ((hcut e).mpr (Or.inl rfl))
  obtain ⟨-, x', hx', hex'⟩ := epOut_ends α β X e' ((hcut e').mpr (Or.inr rfl))
  have hA : ∀ g, ep2A α β X e e' x₁ g = if g = e then epOut α β X e
      else if g = e' ∨ (α g ∈ X ∧ β g ∈ X) then x₁ else α g := fun _ => rfl
  have hB : ∀ g, ep2B α β X e e' x₁ g = if g = e then epOut α β X e'
      else if g = e' ∨ (α g ∈ X ∧ β g ∈ X) then x₁ else β g := fun _ => rfl
  generalize epOut α β X e = a at *
  generalize epOut α β X e' = a' at *
  have hxZ : x ∉ Z := fun h' => hZX _ h' hx
  have hx'Z : x' ∉ Z := fun h' => hZX _ h' hx'
  have hx₁Z : x₁ ∉ Z := fun h' => hZX _ h' hx₁
  have hnl : ∀ g, α g ∈ Z → α g ≠ β g := by
    intro g hg
    rcases h.1 g with h' | h'
    · exact h'.2.2
    · exact absurd (hZL hg) h'.1
  -- profiles of the edges of the contraction
  have hnewE : (ep2A α β X e e' x₁ e = a ∧ ep2B α β X e e' x₁ e = a') := by
    rw [hA, hB, if_pos rfl, if_pos rfl]; exact ⟨rfl, rfl⟩
  have hdead : ∀ g, g ≠ e → (g = e' ∨ (α g ∈ X ∧ β g ∈ X)) →
      (ep2A α β X e e' x₁ g = x₁ ∧ ep2B α β X e e' x₁ g = x₁) := by
    intro g hg hg'
    rw [hA, hB, if_neg hg, if_neg hg, if_pos hg', if_pos hg']; exact ⟨rfl, rfl⟩
  have hother : ∀ g, g ≠ e → ¬(g = e' ∨ (α g ∈ X ∧ β g ∈ X)) →
      (ep2A α β X e e' x₁ g = α g ∧ ep2B α β X e e' x₁ g = β g) := by
    intro g hg hg'
    rw [hA, hB, if_neg hg, if_neg hg, if_neg hg', if_neg hg']; exact ⟨rfl, rfl⟩
  -- the edge relabelling and the comparison
  have key : ∃ σ : E ≃ E, ∀ g, epSame α β (ep2A α β X e e' x₁) (ep2B α β X e e' x₁) Z (σ g) g := by
    by_cases ha' : a' ∈ Z
    · have ha : a ∉ Z := fun h' => hnew ⟨h', ha'⟩
      refine ⟨Equiv.swap e e', fun g => ?_⟩
      by_cases hg : g = e
      · -- `g = e` corresponds to the dead edge `e'`
        rw [hg, Equiv.swap_apply_left]
        have hd := hdead e' (Ne.symm hee') (Or.inl rfl)
        exact epSame_of_ends α β _ _ Z e' e x₁ x₁ a x (Or.inl hd)
          hex.symm
          hx₁Z hxZ (Or.inr ⟨hx₁Z, ha⟩)
      · by_cases hg' : g = e'
        · rw [hg', Equiv.swap_apply_right]
          exact epSame_of_ends α β _ _ Z e e' a' a a' x' (Or.inr ⟨hnewE.1, hnewE.2⟩)
            hex'.symm
            ha hx'Z (Or.inl rfl)
        · rw [Equiv.swap_apply_of_ne_of_ne hg hg']
          by_cases hin : α g ∈ X ∧ β g ∈ X
          · have hd := hdead g hg (Or.inr hin)
            exact epSame_of_ends α β _ _ Z g g x₁ x₁ (α g) (β g) (Or.inl hd)
              (Or.inl ⟨rfl, rfl⟩) hx₁Z (fun h' => hZX _ h' hin.2)
              (Or.inr ⟨hx₁Z, fun h' => hZX _ h' hin.1⟩)
          · have ho := hother g hg (fun h' => h'.elim hg' hin)
            exact epSame_of_eq α β _ _ Z g ho.1 ho.2
    · refine ⟨Equiv.refl E, fun g => ?_⟩
      rw [Equiv.refl_apply]
      by_cases hg : g = e
      · rw [hg]
        exact epSame_of_ends α β _ _ Z e e a a' a x (Or.inl hnewE)
          hex.symm
          ha' hxZ (Or.inl rfl)
      · by_cases hg' : g = e'
        · rw [hg']
          have hd := hdead e' (Ne.symm hee') (Or.inl rfl)
          exact epSame_of_ends α β _ _ Z e' e' x₁ x₁ a' x' (Or.inl hd)
            hex'.symm
            hx₁Z hx'Z (Or.inr ⟨hx₁Z, ha'⟩)
        · by_cases hin : α g ∈ X ∧ β g ∈ X
          · have hd := hdead g hg (Or.inr hin)
            exact epSame_of_ends α β _ _ Z g g x₁ x₁ (α g) (β g) (Or.inl hd)
              (Or.inl ⟨rfl, rfl⟩) hx₁Z (fun h' => hZX _ h' hin.2)
              (Or.inr ⟨hx₁Z, fun h' => hZX _ h' hin.1⟩)
          · have ho := hother g hg (fun h' => h'.elim hg' hin)
            exact epSame_of_eq α β _ _ Z g ho.1 ho.2
  obtain ⟨σ, hσ⟩ := key
  exact ⟨ep_burl_transfer α β _ _ Z σ hnl (fun g c hc => (hσ g).1 c hc) (fun g => (hσ g).2.1)
      (fun g => (hσ g).2.2) hburl,
    ep_cut_card_transfer α β _ _ Z σ (fun g => (hσ g).2.1) (fun g => (hσ g).2.2)⟩

/-- **Lemma 10, first part (in the form of Lemma 7(2) with `k₁ = 1`).** If every live edge of
the contraction of `X` lies in at least `k` perfect matchings, so does every live edge of `G`. -/
theorem epCon_mstar_le {W E : Type*} [Fintype E] (α β : E → W) (L X Y : Finset W)
    (x₀ x₁ y₀ y₁ : W) (h : EpCubicD α β L) (hb : EpBridgeless α β L) (hXL : X ⊆ L)
    (hY : ∀ w, w ∈ Y ↔ w ∈ L ∧ w ∉ X) (hx₀ : x₀ ∈ X) (hy₀ : y₀ ∈ Y) (hy₁ : y₁ ∈ Y)
    (hy : y₁ ≠ y₀) (h3 : (epCut α β X).card = 3) (k : ℕ)
    (h₂ : ∀ g, epConA α β X x₀ x₁ g ∈ epL' L X x₀ →
      k ≤ epMe (epConA α β X x₀ x₁) (epConB α β X x₀ x₁) (epL' L X x₀) g)
    (g : E) (hg : α g ∈ L) : k ≤ epMe α β L g := by
  classical
  have hYL : Y ⊆ L := fun w hw => ((hY w).mp hw).1
  have hcutY : (epCut α β Y).card = 3 := by
    have : epCut α β Y = epCut α β X := by
      ext g'; rw [mem_epCut, mem_epCut]; exact epD_cross_compl α β L X Y h hY g'
    rw [this]; exact h3
  obtain ⟨hc₁, hb₁⟩ := epCon_cubic α β L Y y₀ y₁ h hb hYL hy₀ hy₁ hy hcutY
  have h₁ : ∀ g', epConA α β Y y₀ y₁ g' ∈ epL' L Y y₀ →
      1 ≤ epMe (epConA α β Y y₀ y₁) (epConB α β Y y₀ y₁) (epL' L Y y₀) g' := by
    intro g' hg'
    obtain ⟨M, hM, hgM⟩ := epD_edge_in_pm _ _ _ hc₁ hb₁ g' hg'
    unfold epMe
    exact Finset.card_pos.mpr ⟨M, Finset.mem_filter.mpr ⟨(mem_epPMs _ _ _ _).mpr hM, hgM⟩⟩
  have := ep3_mstar α β L X Y x₀ x₁ y₀ y₁ h hXL hY hx₀ hy₀ 1 k h₁ h₂ g hg
  rwa [one_mul] at this

/-- Ends of an edge of the contraction that has an end in `Z' ⊆ L'`. -/
lemma epCon_ends_mem {W E : Type*} (α β : E → W) (L T Z' : Finset W) (t₀ t₁ : W)
    (ht₀ : t₀ ∈ T) (ht₁ : t₁ ∈ T) (hne : t₁ ≠ t₀) (hZ' : Z' ⊆ epL' L T t₀) (g : E) :
    (epConA α β T t₀ t₁ g ∈ Z' → ¬(α g ∈ T ∧ β g ∈ T) ∧ (α g ∈ Z' ∨ (α g ∈ T ∧ t₀ ∈ Z'))) ∧
    (epConB α β T t₀ t₁ g ∈ Z' → ¬(α g ∈ T ∧ β g ∈ T) ∧ (β g ∈ Z' ∨ (β g ∈ T ∧ t₀ ∈ Z'))) := by
  classical
  have ht₁Z : t₁ ∉ Z' := by
    intro h'
    have := hZ' h'
    unfold epL' at this
    rw [Finset.mem_insert, Finset.mem_sdiff] at this
    rcases this with h'' | ⟨-, h''⟩
    · exact hne h''
    · exact h'' ht₁
  have hA : epConA α β T t₀ t₁ g = if α g ∈ T ∧ β g ∈ T then t₁ else epRho T t₀ (α g) := rfl
  have hB : epConB α β T t₀ t₁ g = if α g ∈ T ∧ β g ∈ T then t₁ else epRho T t₀ (β g) := rfl
  constructor
  · intro h'
    rw [hA] at h'
    by_cases hin : α g ∈ T ∧ β g ∈ T
    · rw [if_pos hin] at h'; exact absurd h' ht₁Z
    · rw [if_neg hin] at h'
      refine ⟨hin, ?_⟩
      unfold epRho at h'
      by_cases ha : α g ∈ T
      · rw [if_pos ha] at h'; exact Or.inr ⟨ha, h'⟩
      · rw [if_neg ha] at h'; exact Or.inl h'
  · intro h'
    rw [hB] at h'
    by_cases hin : α g ∈ T ∧ β g ∈ T
    · rw [if_pos hin] at h'; exact absurd h' ht₁Z
    · rw [if_neg hin] at h'
      refine ⟨hin, ?_⟩
      unfold epRho at h'
      by_cases hb : β g ∈ T
      · rw [if_pos hb] at h'; exact Or.inr ⟨hb, h'⟩
      · rw [if_neg hb] at h'; exact Or.inl h'

/-- Lifting a local matching of the contraction through the contracted set `T`. -/
lemma epCon_lm_lift {W E : Type*} [DecidableEq W] [DecidableEq E] (α β : E → W)
    (L T Z' : Finset W) (t₀ t₁ : W)
    (ht₀ : t₀ ∈ T) (ht₁ : t₁ ∈ T) (hne : t₁ ≠ t₀) (hZ' : Z' ⊆ epL' L T t₀) (htZ : t₀ ∈ Z')
    (N'' : Finset E) (hN'' : N'' ∈ epLM (epConA α β T t₀ t₁) (epConB α β T t₀ t₁) Z')
    (f : E) (hf : f ∈ N'') (hfc : epCross α β T f) (Nf : Finset E)
    (hNf : (∀ g ∈ Nf, α g ∈ T ∧ β g ∈ T ∧ α g ≠ β g) ∧
      ∀ c ∈ T, ∃! g, g ∈ insert f Nf ∧ epCross α β {c} g) :
    N'' ∪ Nf ∈ epLM α β (Z' ∪ T) := by
  have hnin : ∀ g ∈ N'', ¬(α g ∈ T ∧ β g ∈ T) := by
    intro g hg
    have a := epCon_ends_mem α β L T Z' t₀ t₁ ht₀ ht₁ hne hZ' g
    rcases hN''.1 g hg with h' | h'
    · exact (a.1 h').1
    · exact (a.2 h').1
  have hsub : ({t₀} : Finset W) ⊆ epL' L T t₀ := Finset.singleton_subset_iff.mpr (hZ' htZ)
  have hcutu : ∃! g, g ∈ N'' ∧ epCross α β T g := by
    have := hN''.2 t₀ htZ
    simpa only [epCon_cross α β L T t₀ t₁ ht₀ {t₀} hsub, epLift_singleton_t₀ T t₀ ht₀] using this
  refine ⟨fun g hg => ?_, fun c hc => ?_⟩
  · rcases Finset.mem_union.mp hg with h' | h'
    · have a := epCon_ends_mem α β L T Z' t₀ t₁ ht₀ ht₁ hne hZ' g
      rcases hN''.1 g h' with h'' | h''
      · rcases (a.1 h'').2 with h3 | ⟨h3, -⟩
        · exact Or.inl (Finset.mem_union_left _ h3)
        · exact Or.inl (Finset.mem_union_right _ h3)
      · rcases (a.2 h'').2 with h3 | ⟨h3, -⟩
        · exact Or.inr (Finset.mem_union_left _ h3)
        · exact Or.inr (Finset.mem_union_right _ h3)
    · exact Or.inl (Finset.mem_union_right _ (hNf.1 g h').1)
  · by_cases hcT : c ∈ T
    · obtain ⟨g₀, ⟨h1, h2⟩, huniq⟩ := hNf.2 c hcT
      have hg₀ : g₀ ∈ N'' ∪ Nf := by
        rcases Finset.mem_insert.mp h1 with h' | h'
        · exact Finset.mem_union_left _ (h' ▸ hf)
        · exact Finset.mem_union_right _ h'
      refine ⟨g₀, ⟨hg₀, h2⟩, ?_⟩
      rintro g ⟨hg, hgc⟩
      rcases Finset.mem_union.mp hg with h' | h'
      · have hgT : epCross α β T g := by
          have hn := hnin g h'
          rw [epCross_singleton] at hgc
          unfold epCross
          rcases hgc with ⟨h3, -⟩ | ⟨-, h3⟩
          · left; exact ⟨h3 ▸ hcT, fun hb => hn ⟨h3 ▸ hcT, hb⟩⟩
          · right; exact ⟨fun ha => hn ⟨ha, h3 ▸ hcT⟩, h3 ▸ hcT⟩
        have hgf : g = f := hcutu.unique ⟨h', hgT⟩ ⟨hf, hfc⟩
        exact huniq g ⟨Finset.mem_insert.mpr (Or.inl hgf), hgc⟩
      · exact huniq g ⟨Finset.mem_insert_of_mem h', hgc⟩
    · have hcZ : c ∈ Z' := (Finset.mem_union.mp hc).resolve_right hcT
      have hc' : ({c} : Finset W) ⊆ epL' L T t₀ := Finset.singleton_subset_iff.mpr (hZ' hcZ)
      have hct : c ≠ t₀ := fun h' => hcT (h' ▸ ht₀)
      have := hN''.2 c hcZ
      simp only [epCon_cross α β L T t₀ t₁ ht₀ {c} hc', epLift_singleton_ne T t₀ c hct] at this
      refine ep_split_unique α β N'' Nf c this ?_
      intro g hg hcr
      rw [epCross_singleton] at hcr
      rcases hcr with ⟨h', -⟩ | ⟨-, h'⟩
      · exact hcT (h' ▸ (hNf.1 g hg).1)
      · exact hcT (h' ▸ (hNf.1 g hg).2.1)

open Classical in
/-- Restricting a local matching of `Z' ∪ T` with exactly one edge in `δ(T)` to the
contraction. -/
lemma epCon_lm_restrict {W E : Type*} [Fintype E] (α β : E → W) (L T Z' : Finset W)
    (t₀ t₁ : W) (ht₀ : t₀ ∈ T) (hZ' : Z' ⊆ epL' L T t₀) (htZ : t₀ ∈ Z')
    (N : Finset E) (hN : N ∈ epLM α β (Z' ∪ T))
    (hone : ∃! g, g ∈ N ∧ epCross α β T g) :
    N.filter (fun g => ¬(α g ∈ T ∧ β g ∈ T)) ∈
      epLM (epConA α β T t₀ t₁) (epConB α β T t₀ t₁) Z' := by
  have hZ'T : ∀ c, c ∈ Z' → c ≠ t₀ → c ∉ T := by
    intro c hc hct hcT
    have := hZ' hc
    unfold epL' at this
    rw [Finset.mem_insert, Finset.mem_sdiff] at this
    rcases this with h' | ⟨-, h'⟩
    · exact hct h'
    · exact h' hcT
  refine ⟨fun g hg => ?_, fun c hc => ?_⟩
  · rw [Finset.mem_filter] at hg
    obtain ⟨hgN, hnin⟩ := hg
    have hA : epConA α β T t₀ t₁ g = epRho T t₀ (α g) := by unfold epConA; rw [if_neg hnin]
    have hB : epConB α β T t₀ t₁ g = epRho T t₀ (β g) := by unfold epConB; rw [if_neg hnin]
    rw [hA, hB]
    have hρ : ∀ w, w ∈ Z' ∪ T → epRho T t₀ w ∈ Z' := by
      intro w hw
      unfold epRho
      by_cases hwT : w ∈ T
      · rw [if_pos hwT]; exact htZ
      · rw [if_neg hwT]; exact (Finset.mem_union.mp hw).resolve_right hwT
    rcases hN.1 g hgN with h' | h'
    · exact Or.inl (hρ _ h')
    · exact Or.inr (hρ _ h')
  · have hc' : ({c} : Finset W) ⊆ epL' L T t₀ := Finset.singleton_subset_iff.mpr (hZ' hc)
    simp only [epCon_cross α β L T t₀ t₁ ht₀ {c} hc']
    by_cases hct : c = t₀
    · rw [hct, epLift_singleton_t₀ T t₀ ht₀]
      obtain ⟨g₀, ⟨h1, h2⟩, huniq⟩ := hone
      refine ⟨g₀, ⟨Finset.mem_filter.mpr ⟨h1, ?_⟩, h2⟩,
        fun g hg => huniq g ⟨(Finset.mem_filter.mp hg.1).1, hg.2⟩⟩
      unfold epCross at h2; tauto
    · rw [epLift_singleton_ne T t₀ c hct]
      have hcT := hZ'T c hc hct
      obtain ⟨g₀, ⟨h1, h2⟩, huniq⟩ := hN.2 c (Finset.mem_union_left _ hc)
      refine ⟨g₀, ⟨Finset.mem_filter.mpr ⟨h1, ?_⟩, h2⟩,
        fun g hg => huniq g ⟨(Finset.mem_filter.mp hg.1).1, hg.2⟩⟩
      rw [epCross_singleton] at h2
      rintro ⟨ha, hb⟩
      rcases h2 with ⟨h3, -⟩ | ⟨-, h3⟩
      · exact hcT (h3 ▸ ha)
      · exact hcT (h3 ▸ hb)

open Classical in
/-- Parity of cuts in a cubic multigraph with dead edges. -/
lemma epD_cut_parity {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (h : EpCubicD α β L) (T : Finset W) (hT : T ⊆ L) :
    (epCut α β T).card % 2 = T.card % 2 := by
  have hc := epD_live_cubic α β L h
  rw [← epD_cut_card α β L h T]
  have hd := ep_double_count (fun e : {e : E // α e ∈ L} => α e.1) (fun e => β e.1)
    Finset.univ (fun e _ => hc.2.1 e) T
  have h3 : ∀ c ∈ T, (Finset.univ.filter (epCross (fun e : {e : E // α e ∈ L} => α e.1)
      (fun e => β e.1) {c})).card = 3 := fun c hcT => hc.2.2 c (hT hcT)
  rw [Finset.sum_congr rfl h3, Finset.sum_const, smul_eq_mul] at hd
  unfold epCut
  omega

open Classical in
/-- **Claim 3 with dead edges.** -/
lemma epD_claim3 {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (h : EpCubicD α β L)
    (X Y : Finset W) (hXL : X ⊆ L) (hYX : Y ⊆ X) (hY : (epCut α β Y).card = 3)
    (p : Finset E → ℝ) (hp : EpBalanced α β X p) (M : Finset E) (hM : p M ≠ 0) :
    ∃! g, g ∈ M ∧ epCross α β Y g := by
  obtain ⟨hp0, hpS, hp1, hpb⟩ := hp
  have hYodd : Y.card % 2 = 1 := by
    rw [← epD_cut_parity α β L h Y (hYX.trans hXL), hY]
  have hodd : ∀ N, N ∈ epLM α β X → 1 ≤ (N.filter (epCross α β Y)).card := by
    intro N hN
    have hnl : ∀ e ∈ N, α e ≠ β e := by
      intro e he
      rcases h.1 e with h' | h'
      · exact h'.2.2
      · exact absurd (epD_live_of_mem_lm h X hXL hN e he).1 h'.1
    have hd := ep_double_count α β N hnl Y
    have h1 : ∀ c ∈ Y, (N.filter (epCross α β {c})).card = 1 :=
      fun c hcY => (ep_unique_iff_card N _).mp (hN.2 c (hYX hcY))
    rw [Finset.sum_congr rfl h1, Finset.sum_const, smul_eq_mul, mul_one] at hd
    omega
  have hexp : ∑ N, p N * ((N.filter (epCross α β Y)).card : ℝ) = 1 := by
    have : ∀ N, p N * ((N.filter (epCross α β Y)).card : ℝ) =
        ∑ e ∈ epCut α β Y, p N * epInd N e := by
      intro N; rw [← Finset.mul_sum, ep_sum_ind_cut]
    rw [Finset.sum_congr rfl (fun N _ => this N), Finset.sum_comm]
    have h3 : ∀ e ∈ epCut α β Y, ∑ N, p N * epInd N e = 1 / 3 := by
      intro e he
      refine hpb e ?_
      rw [mem_epCut] at he
      rcases he with ⟨h', -⟩ | ⟨-, h'⟩
      · exact Or.inl (hYX h')
      · exact Or.inr (hYX h')
    rw [Finset.sum_congr rfl h3, Finset.sum_const, hY]; norm_num
  have hzero : ∑ N, p N * (((N.filter (epCross α β Y)).card : ℝ) - 1) = 0 := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hexp, hp1, sub_self]
  have hnn : ∀ N ∈ (Finset.univ : Finset (Finset E)),
      0 ≤ p N * (((N.filter (epCross α β Y)).card : ℝ) - 1) := by
    intro N _
    by_cases hN : p N = 0
    · rw [hN, zero_mul]
    · have : (1 : ℝ) ≤ ((N.filter (epCross α β Y)).card : ℝ) := by
        exact_mod_cast hodd N (hpS N hN)
      exact mul_nonneg (hp0 N) (by linarith)
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hzero M (Finset.mem_univ _)
  have h1 := (mul_eq_zero.mp this).resolve_left hM
  have h2 : ((M.filter (epCross α β Y)).card : ℝ) = 1 := by linarith
  rw [ep_unique_iff_card]
  exact_mod_cast h2

set_option maxHeartbeats 3200000 in
open Classical in
/-- Alternating families lift from the contraction of `T` to `G`, when every cut edge of `T`
extends to a matching of `T` by edges inside `T`. -/
lemma epCon_alt_lift {W E : Type*} [Fintype E] (α β : E → W) (L T Z' : Finset W)
    (t₀ t₁ : W) (ht₀ : t₀ ∈ T) (ht₁ : t₁ ∈ T) (hne : t₁ ≠ t₀)
    (Nf : E → Finset E)
    (hfc : ∀ f, epCross α β T f → (∀ g ∈ Nf f, α g ∈ T ∧ β g ∈ T ∧ α g ≠ β g) ∧
      ∀ c ∈ T, ∃! g, g ∈ insert f (Nf f) ∧ epCross α β {c} g)
    (hZ' : Z' ⊆ epL' L T t₀) (htZ : t₀ ∈ Z') (N : Finset E) (hN : N ∈ epLM α β (Z' ∪ T))
    (hone : ∃! g, g ∈ N ∧ epCross α β T g) (k : ℕ)
    (hk : EpAlt (epConA α β T t₀ t₁) (epConB α β T t₀ t₁) Z'
      (N.filter (fun g => ¬(α g ∈ T ∧ β g ∈ T))) k) :
    EpAlt α β (Z' ∪ T) N k := by
  obtain ⟨D', hne', hin', hflip', hdisj'⟩ := hk
  have hZ'T : ∀ c, c ∈ Z' → c ≠ t₀ → c ∉ T := by
    intro c hc hct hcT
    have := hZ' hc
    unfold epL' at this
    rw [Finset.mem_insert, Finset.mem_sdiff] at this
    rcases this with h' | ⟨-, h'⟩
    · exact hct h'
    · exact h' hcT
  have hcrT : ∀ g, epCross (epConA α β T t₀ t₁) (epConB α β T t₀ t₁) {t₀} g ↔
      epCross α β T g := by
    intro g
    rw [epCon_cross α β L T t₀ t₁ ht₀ {t₀} (Finset.singleton_subset_iff.mpr (hZ' htZ)),
      epLift_singleton_t₀ T t₀ ht₀]
  have hcr : ∀ c, c ∈ Z' → c ∉ T → ∀ g,
      (epCross (epConA α β T t₀ t₁) (epConB α β T t₀ t₁) {c} g ↔ epCross α β {c} g) := by
    intro c hc hcT g
    rw [epCon_cross α β L T t₀ t₁ ht₀ {c} (Finset.singleton_subset_iff.mpr (hZ' hc)),
      epLift_singleton_ne T t₀ c (fun h' => hcT (h' ▸ ht₀))]
  -- edges of the `D' i` in terms of `G`
  have hD'in : ∀ i g, g ∈ D' i → ¬(α g ∈ T ∧ β g ∈ T) ∧ α g ∈ Z' ∪ T ∧ β g ∈ Z' ∪ T := by
    intro i g hg
    have a := epCon_ends_mem α β L T Z' t₀ t₁ ht₀ ht₁ hne hZ' g
    have b := hin' i g hg
    refine ⟨(a.1 b.1).1, ?_, ?_⟩
    · rcases (a.1 b.1).2 with h' | ⟨h', -⟩
      · exact Finset.mem_union_left _ h'
      · exact Finset.mem_union_right _ h'
    · rcases (a.2 b.2).2 with h' | ⟨h', -⟩
      · exact Finset.mem_union_left _ h'
      · exact Finset.mem_union_right _ h'
  have hcrossT : ∀ g c, ¬(α g ∈ T ∧ β g ∈ T) → c ∈ T → epCross α β {c} g →
      epCross α β T g := by
    intro g c hn hcT hgc
    rw [epCross_singleton] at hgc
    unfold epCross
    rcases hgc with ⟨h3, -⟩ | ⟨-, h3⟩
    · left; exact ⟨h3 ▸ hcT, fun hb => hn ⟨h3 ▸ hcT, hb⟩⟩
    · right; exact ⟨fun ha => hn ⟨ha, h3 ▸ hcT⟩, h3 ▸ hcT⟩
  -- an edge of `D' i` meeting `c` in `G` meets the image of `c` in the contraction
  have hD'touch : ∀ i g c, g ∈ D' i → epCross α β {c} g →
      epCross (epConA α β T t₀ t₁) (epConB α β T t₀ t₁) {if c ∈ T then t₀ else c} g := by
    intro i g c hg hgc
    obtain ⟨hn, ha, hb⟩ := hD'in i g hg
    by_cases hcT : c ∈ T
    · rw [if_pos hcT, hcrT]; exact hcrossT g c hn hcT hgc
    · rw [if_neg hcT]
      have hcZ : c ∈ Z' := by
        rw [epCross_singleton] at hgc
        rcases hgc with ⟨h3, -⟩ | ⟨-, h3⟩
        · exact (Finset.mem_union.mp (h3 ▸ ha)).resolve_right hcT
        · exact (Finset.mem_union.mp (h3 ▸ hb)).resolve_right hcT
      exact (hcr c hcZ hcT g).mpr hgc
  -- the unique cut edge of each flipped matching
  have hcutR : ∀ i, ∃! g, g ∈ symmDiff (N.filter (fun g => ¬(α g ∈ T ∧ β g ∈ T))) (D' i) ∧
      epCross α β T g := by
    intro i
    have := (hflip' i).2 t₀ htZ
    simpa only [hcrT] using this
  choose f₂ hf₂ hf₂u using hcutR
  have hLift : ∀ i, symmDiff (N.filter (fun g => ¬(α g ∈ T ∧ β g ∈ T))) (D' i) ∪ Nf (f₂ i) ∈
      epLM α β (Z' ∪ T) := fun i =>
    epCon_lm_lift α β L T Z' t₀ t₁ ht₀ ht₁ hne hZ' htZ _ (hflip' i) (f₂ i) (hf₂ i).1 (hf₂ i).2
      (Nf (f₂ i)) (hfc _ (hf₂ i).2)
  -- membership in the modified flip set
  have hK1 : ∀ i g, g ∈ symmDiff N
      (symmDiff (N.filter (fun g => ¬(α g ∈ T ∧ β g ∈ T))) (D' i) ∪ Nf (f₂ i)) →
      (α g ∈ T ∧ β g ∈ T) ∨ g ∈ D' i := by
    intro i g hg
    by_cases hinT : α g ∈ T ∧ β g ∈ T
    · exact Or.inl hinT
    · right
      have hNf : g ∉ Nf (f₂ i) := fun h' =>
        hinT ⟨((hfc _ (hf₂ i).2).1 g h').1, ((hfc _ (hf₂ i).2).1 g h').2.1⟩
      simp only [Finset.mem_symmDiff, Finset.mem_union, Finset.mem_filter] at hg
      tauto
  obtain ⟨D, hD⟩ : ∃ D : Fin k → Finset E, ∀ i, D i =
      if epTouch (epConA α β T t₀ t₁) (epConB α β T t₀ t₁) (D' i) t₀ then
        symmDiff N (symmDiff (N.filter (fun g => ¬(α g ∈ T ∧ β g ∈ T))) (D' i) ∪ Nf (f₂ i))
      else D' i := ⟨fun i => _, fun i => rfl⟩
  refine ⟨D, fun i => ?_, fun i g hg => ?_, fun i => ?_, fun i j hij c => ?_⟩
  · -- nonempty
    by_cases ht : epTouch (epConA α β T t₀ t₁) (epConB α β T t₀ t₁) (D' i) t₀
    · rw [hD i, if_pos ht, Finset.nonempty_iff_ne_empty]
      intro hempty
      have hEq : N = symmDiff (N.filter (fun g => ¬(α g ∈ T ∧ β g ∈ T))) (D' i) ∪ Nf (f₂ i) :=
        symmDiff_eq_bot.mp hempty
      obtain ⟨g, hg⟩ := hne' i
      have hgn := (hD'in i g hg).1
      have hNf : g ∉ Nf (f₂ i) := fun h' =>
        hgn ⟨((hfc _ (hf₂ i).2).1 g h').1, ((hfc _ (hf₂ i).2).1 g h').2.1⟩
      have h1 : g ∈ N ↔ g ∈ symmDiff (N.filter (fun g => ¬(α g ∈ T ∧ β g ∈ T))) (D' i) ∪
          Nf (f₂ i) := by rw [← hEq]
      simp only [Finset.mem_symmDiff, Finset.mem_union, Finset.mem_filter] at h1
      tauto
    · rw [hD i, if_neg ht]; exact hne' i
  · -- inside `Z' ∪ T`
    by_cases ht : epTouch (epConA α β T t₀ t₁) (epConB α β T t₀ t₁) (D' i) t₀
    · rw [hD i, if_pos ht] at hg
      rcases hK1 i g hg with h' | h'
      · exact ⟨Finset.mem_union_right _ h'.1, Finset.mem_union_right _ h'.2⟩
      · exact (hD'in i g h').2
    · rw [hD i, if_neg ht] at hg; exact (hD'in i g hg).2
  · -- flip
    by_cases ht : epTouch (epConA α β T t₀ t₁) (epConB α β T t₀ t₁) (D' i) t₀
    · rw [hD i, if_pos ht, symmDiff_symmDiff_cancel_left]; exact hLift i
    · rw [hD i, if_neg ht]
      have hnoT : ∀ c, c ∈ T → ∀ g ∈ D' i, ¬epCross α β {c} g := by
        intro c hcT g hg hgc
        have := hD'touch i g c hg hgc
        rw [if_pos hcT] at this
        exact ht ⟨g, hg, this⟩
      refine ⟨fun g hg => ?_, fun c hc => ?_⟩
      · rcases Finset.mem_symmDiff.mp hg with ⟨h', -⟩ | ⟨h', -⟩
        · exact hN.1 g h'
        · exact Or.inl (hD'in i g h').2.1
      · by_cases hcT : c ∈ T
        · obtain ⟨g₀, ⟨h1, h2⟩, huniq⟩ := hN.2 c hc
          refine ⟨g₀, ⟨Finset.mem_symmDiff.mpr (Or.inl ⟨h1, fun h' => hnoT c hcT g₀ h' h2⟩),
            h2⟩, ?_⟩
          rintro g ⟨hg, hgc⟩
          rcases Finset.mem_symmDiff.mp hg with ⟨h', -⟩ | ⟨h', -⟩
          · exact huniq g ⟨h', hgc⟩
          · exact absurd hgc (hnoT c hcT g h')
        · have hcZ : c ∈ Z' := (Finset.mem_union.mp hc).resolve_right hcT
          obtain ⟨g₀, ⟨h1, h2⟩, huniq⟩ := (hflip' i).2 c hcZ
          have hmem : ∀ g, epCross α β {c} g →
              (g ∈ symmDiff N (D' i) ↔
                g ∈ symmDiff (N.filter (fun g => ¬(α g ∈ T ∧ β g ∈ T))) (D' i)) := by
            intro g hgc
            have hn : ¬(α g ∈ T ∧ β g ∈ T) := by
              rw [epCross_singleton] at hgc
              rintro ⟨ha, hb⟩
              rcases hgc with ⟨h3, -⟩ | ⟨-, h3⟩
              · exact hcT (h3 ▸ ha)
              · exact hcT (h3 ▸ hb)
            simp only [Finset.mem_symmDiff, Finset.mem_filter]
            tauto
          have h2' := (hcr c hcZ hcT g₀).mp h2
          refine ⟨g₀, ⟨(hmem g₀ h2').mpr h1, h2'⟩, ?_⟩
          rintro g ⟨hg, hgc⟩
          exact huniq g ⟨(hmem g hgc).mp hg, (hcr c hcZ hcT g).mpr hgc⟩
  · -- disjointness
    have hK2 : ∀ i, epTouch α β (D i) c →
        epTouch (epConA α β T t₀ t₁) (epConB α β T t₀ t₁) (D' i) (if c ∈ T then t₀ else c) := by
      rintro i ⟨g, hg, hgc⟩
      by_cases ht : epTouch (epConA α β T t₀ t₁) (epConB α β T t₀ t₁) (D' i) t₀
      · rw [hD i, if_pos ht] at hg
        by_cases hcT : c ∈ T
        · rw [if_pos hcT]; exact ht
        · rcases hK1 i g hg with h' | h'
          · exfalso
            rw [epCross_singleton] at hgc
            rcases hgc with ⟨h3, -⟩ | ⟨-, h3⟩
            · exact hcT (h3 ▸ h'.1)
            · exact hcT (h3 ▸ h'.2)
          · exact ⟨g, h', hD'touch i g c h' hgc⟩
      · rw [hD i, if_neg ht] at hg
        exact ⟨g, hg, hD'touch i g c hg hgc⟩
    rintro ⟨h1, h2⟩
    exact hdisj' i j hij _ ⟨hK2 i h1, hK2 j h2⟩

set_option maxHeartbeats 1600000 in
open Classical in
/-- **Lemma 10, second part (general form).** Let `T` have a cut of size three, and suppose
every cut edge of `T` extends to a matching of `T` by edges inside `T` (as for a triangle).
If `Z'` is a burl of the contraction of `T` containing the new vertex `t₀`, then `Z' ∪ T` is a
burl of `G`. -/
theorem epCon_burl_lift {W E : Type*} [Fintype E] (α β : E → W) (L T Z' : Finset W)
    (t₀ t₁ : W) (h : EpCubicD α β L) (hTL : T ⊆ L) (ht₀ : t₀ ∈ T) (ht₁ : t₁ ∈ T)
    (hne : t₁ ≠ t₀) (h3 : (epCut α β T).card = 3) (Nf : E → Finset E)
    (hfc : ∀ f, epCross α β T f → (∀ g ∈ Nf f, α g ∈ T ∧ β g ∈ T ∧ α g ≠ β g) ∧
      ∀ c ∈ T, ∃! g, g ∈ insert f (Nf f) ∧ epCross α β {c} g)
    (hZ' : Z' ⊆ epL' L T t₀) (htZ : t₀ ∈ Z')
    (hburl : EpBurl (epConA α β T t₀ t₁) (epConB α β T t₀ t₁) Z') :
    EpBurl α β (Z' ∪ T) := by
  intro p hp
  have hZL : Z' ∪ T ⊆ L := by
    intro w hw
    rcases Finset.mem_union.mp hw with h' | h'
    · have := hZ' h'
      unfold epL' at this
      rw [Finset.mem_insert, Finset.mem_sdiff] at this
      rcases this with h'' | ⟨h'', -⟩
      · exact h'' ▸ hTL ht₀
      · exact h''
    · exact hTL h'
  have hone : ∀ N, p N ≠ 0 → ∃! g, g ∈ N ∧ epCross α β T g := fun N hN =>
    epD_claim3 α β L h (Z' ∪ T) T hZL Finset.subset_union_right h3 p hp N hN
  obtain ⟨hp0, hpS, hp1, hpb⟩ := hp
  have hpush : ∀ f : Finset E → ℝ,
      ∑ N', (∑ N, if N.filter (fun g => ¬(α g ∈ T ∧ β g ∈ T)) = N' then p N else 0) * f N' =
        ∑ N, p N * f (N.filter (fun g => ¬(α g ∈ T ∧ β g ∈ T))) := by
    intro f
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun N _ => ?_
    rw [Finset.sum_eq_single (N.filter (fun g => ¬(α g ∈ T ∧ β g ∈ T)))]
    · rw [if_pos rfl]
    · intro N' _ hN'; rw [if_neg (Ne.symm hN'), zero_mul]
    · intro h'; exact absurd (Finset.mem_univ _) h'
  have hbal : EpBalanced (epConA α β T t₀ t₁) (epConB α β T t₀ t₁) Z'
      (fun N' => ∑ N, if N.filter (fun g => ¬(α g ∈ T ∧ β g ∈ T)) = N' then p N else 0) := by
    refine ⟨fun N' => Finset.sum_nonneg fun N _ => by split_ifs; exact hp0 N; exact le_refl _,
      fun N' hN' => ?_, ?_, fun g' hg' => ?_⟩
    · obtain ⟨N, -, hN⟩ := Finset.exists_ne_zero_of_sum_ne_zero hN'
      have hNN' : N.filter (fun g => ¬(α g ∈ T ∧ β g ∈ T)) = N' := by
        by_contra h'; exact hN (if_neg h')
      rw [if_pos hNN'] at hN
      rw [← hNN']
      exact epCon_lm_restrict α β L T Z' t₀ t₁ ht₀ hZ' htZ N (hpS N hN) (hone N hN)
    · have := hpush (fun _ => 1)
      simp only [mul_one] at this
      rw [this, hp1]
    · rw [hpush (fun N' => epInd N' g')]
      have a := epCon_ends_mem α β L T Z' t₀ t₁ ht₀ ht₁ hne hZ' g'
      have hnin : ¬(α g' ∈ T ∧ β g' ∈ T) := by
        rcases hg' with h' | h'
        · exact (a.1 h').1
        · exact (a.2 h').1
      have hEZ : α g' ∈ Z' ∪ T ∨ β g' ∈ Z' ∪ T := by
        rcases hg' with h' | h'
        · rcases (a.1 h').2 with h'' | ⟨h'', -⟩
          · exact Or.inl (Finset.mem_union_left _ h'')
          · exact Or.inl (Finset.mem_union_right _ h'')
        · rcases (a.2 h').2 with h'' | ⟨h'', -⟩
          · exact Or.inr (Finset.mem_union_left _ h'')
          · exact Or.inr (Finset.mem_union_right _ h'')
      rw [← hpb g' hEZ]
      refine Finset.sum_congr rfl fun N _ => ?_
      congr 1
      unfold epInd
      simp only [Finset.mem_filter, hnin, not_false_eq_true, and_true]
  have h1 := hburl _ hbal
  rw [hpush (fun N' => (epAltNum (epConA α β T t₀ t₁) (epConB α β T t₀ t₁) Z' N' : ℝ))] at h1
  refine h1.trans (Finset.sum_le_sum fun N _ => ?_)
  by_cases hN : p N = 0
  · rw [hN, zero_mul, zero_mul]
  · refine mul_le_mul_of_nonneg_left ?_ (hp0 N)
    have hnl : ∀ e, α e ∈ Z' ∪ T → α e ≠ β e := by
      intro e he
      rcases h.1 e with h' | h'
      · exact h'.2.2
      · exact absurd (hZL he) h'.1
    exact_mod_cast epAlt_le_altNum' α β (Z' ∪ T) hnl N _
      (epCon_alt_lift α β L T Z' t₀ t₁ ht₀ ht₁ hne Nf hfc hZ' htZ N (hpS N hN) (hone N hN) _
        (epAltNum_spec _ _ Z' _))

open Classical in
/-- **Lemma 5(1) with dead edges.** For every live edge `e` there are two distinct perfect
matchings avoiding `e`. -/
lemma epD_two_pm_avoiding {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (h : EpCubicD α β L) (hb : EpBridgeless α β L) (e : E) (he : α e ∈ L) :
    ∃ M₁ M₂, M₁ ∈ epPM α β L ∧ M₂ ∈ epPM α β L ∧ M₁ ≠ M₂ ∧ e ∉ M₁ ∧ e ∉ M₂ := by
  have hne : α e ≠ β e := by
    rcases h.1 e with h' | h'
    · exact h'.2.2
    · exact absurd he h'.1
  have hcard := h.2 (α e) he
  have hecr : epCross α β {α e} e := (ep_cross_ends α β e hne _).mpr (Or.inl rfl)
  have hecut : e ∈ epCut α β {α e} := (mem_epCut _ _ _ _).mpr hecr
  have h2 : ((epCut α β {α e}).erase e).card = 2 := by
    rw [Finset.card_erase_of_mem hecut, hcard]
  obtain ⟨f, g, hfg, hfgs⟩ := Finset.card_eq_two.mp h2
  have hf : f ≠ e ∧ epCross α β {α e} f := by
    have : f ∈ (epCut α β {α e}).erase e := by rw [hfgs]; exact Finset.mem_insert_self _ _
    exact ⟨Finset.ne_of_mem_erase this, (mem_epCut _ _ _ _).mp (Finset.mem_of_mem_erase this)⟩
  have hg : g ≠ e ∧ epCross α β {α e} g := by
    have : g ∈ (epCut α β {α e}).erase e := by
      rw [hfgs]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    exact ⟨Finset.ne_of_mem_erase this, (mem_epCut _ _ _ _).mp (Finset.mem_of_mem_erase this)⟩
  obtain ⟨M₁, hM₁, hfM⟩ := epD_edge_in_pm α β L h hb f (epD_live_of_cross h _ f hf.2).1
  obtain ⟨M₂, hM₂, hgM⟩ := epD_edge_in_pm α β L h hb g (epD_live_of_cross h _ g hg.2).1
  have hu₁ := hM₁.2 (α e) he
  have hu₂ := hM₂.2 (α e) he
  refine ⟨M₁, M₂, hM₁, hM₂, ?_, ?_, ?_⟩
  · intro h'
    exact hfg (hu₂.unique ⟨h' ▸ hfM, hf.2⟩ ⟨hgM, hg.2⟩)
  · intro h'; exact hf.1 (hu₁.unique ⟨hfM, hf.2⟩ ⟨h', hecr⟩)
  · intro h'; exact hg.1 (hu₂.unique ⟨hgM, hg.2⟩ ⟨h', hecr⟩)

open Classical in
/-- Two distinct local matchings that differ only inside `X` give `a(G, X, M) ≥ 1`
(version without loops at vertices of `X` only). -/
lemma ep_two_LM_altNum' {W E : Type*} [Fintype E] (α β : E → W) (X : Finset W)
    (hnl : ∀ e, α e ∈ X → α e ≠ β e) {M M' : Finset E} (hM' : M' ∈ epLM α β X) (hne : M ≠ M')
    (hin : ∀ e ∈ symmDiff M M', α e ∈ X ∧ β e ∈ X) : 1 ≤ epAltNum α β X M := by
  refine epAlt_le_altNum' α β X hnl M 1 ⟨fun _ => symmDiff M M', fun _ => ?_, fun _ => hin,
    fun _ => ?_, fun i j hij => absurd (Subsingleton.elim i j) hij⟩
  · rw [Finset.nonempty_iff_ne_empty]
    intro h
    exact hne (symmDiff_eq_bot.mp h)
  · show symmDiff M (symmDiff M M') ∈ epLM α β X
    rw [symmDiff_symmDiff_cancel_left]; exact hM'

set_option maxHeartbeats 1600000 in
open Classical in
/-- **Lemma 6, 2-twigs.** A vertex set with a cut of size two is a burl. -/
theorem ep_twig2_burl {W E : Type*} [Fintype E] (α β : E → W) (L X Y : Finset W) (e e' : E)
    (y₁ : W) (h : EpCubicD α β L) (hb : EpBridgeless α β L) (hXL : X ⊆ L)
    (hY : ∀ w, w ∈ Y ↔ w ∈ L ∧ w ∉ X) (hy₁ : y₁ ∈ Y) (hee' : e ≠ e')
    (hcut : ∀ g, epCross α β X g ↔ g = e ∨ g = e') : EpBurl α β X := by
  have hYL : Y ⊆ L := fun w hw => ((hY w).mp hw).1
  have hXY : ∀ w, w ∈ L \ Y ↔ w ∈ X := by
    intro w
    rw [Finset.mem_sdiff]
    constructor
    · rintro ⟨h1, h2⟩; by_contra h'; exact h2 ((hY w).mpr ⟨h1, h'⟩)
    · intro hw; exact ⟨hXL hw, fun h' => ((hY w).mp h').2 hw⟩
  have hcutY := ep2_cut_compl α β L X Y e e' h hY hcut
  obtain ⟨hcub, hbr⟩ := ep2_cubic α β L Y e e' y₁ h hb hYL hy₁ hee' hcutY
  have hnl : ∀ g, α g ∈ X → α g ≠ β g := by
    intro g hg
    rcases h.1 g with h' | h'
    · exact h'.2.2
    · exact absurd (hXL hg) h'.1
  -- the new edge is live in the contraction
  have helive : ep2A α β Y e e' y₁ e ∈ L \ Y := by
    obtain ⟨a1, a2, -, -⟩ := ep_cut_insert_card α β L Y h hb hYL e e' hee' hcutY e (Or.inl rfl)
    have : ep2A α β Y e e' y₁ e = epOut α β Y e := by unfold ep2A; rw [if_pos rfl]
    rw [this]; exact Finset.mem_sdiff.mpr ⟨a1, a2⟩
  obtain ⟨M₁, M₂, hM₁, hM₂, hM12, heM₁, heM₂⟩ :=
    epD_two_pm_avoiding _ _ (L \ Y) hcub hbr e helive
  have hAB : ∀ g, g ≠ e → ¬(g = e' ∨ (α g ∈ Y ∧ β g ∈ Y)) →
      ep2A α β Y e e' y₁ g = α g ∧ ep2B α β Y e e' y₁ g = β g := by
    intro g hg hg'
    unfold ep2A ep2B
    rw [if_neg hg, if_neg hg, if_neg hg', if_neg hg']
    exact ⟨rfl, rfl⟩
  -- a perfect matching of the contraction avoiding `e` is a local matching inside `X`
  have hback : ∀ N, N ∈ epPM (ep2A α β Y e e' y₁) (ep2B α β Y e e' y₁) (L \ Y) → e ∉ N →
      N ∈ epLM α β X ∧ ∀ g ∈ N, α g ∈ X ∧ β g ∈ X := by
    intro N hN heN
    have hedge : ∀ g ∈ N, g ≠ e ∧ g ≠ e' ∧ α g ∈ X ∧ β g ∈ X ∧ ¬(α g ∈ Y ∧ β g ∈ Y) := by
      intro g hg
      have hge : g ≠ e := fun h' => heN (h' ▸ hg)
      have a := ep2_pm_outside α β (L \ Y) Y e e' y₁ hcutY hN g hg hge
      have hl : α g ∈ L ∧ β g ∈ L := by
        rcases h.1 g with h' | h'
        · exact ⟨h'.1, h'.2.1⟩
        · exact absurd h'.2.symm a.2.1
      exact ⟨hge, a.1, (hXY _).mp (Finset.mem_sdiff.mpr ⟨hl.1, a.2.2.1⟩),
        (hXY _).mp (Finset.mem_sdiff.mpr ⟨hl.2, a.2.2.2⟩), fun h' => a.2.2.1 h'.1⟩
    refine ⟨⟨fun g hg => Or.inl (hedge g hg).2.2.1, fun c hc => ?_⟩,
      fun g hg => ⟨(hedge g hg).2.2.1, (hedge g hg).2.2.2.1⟩⟩
    obtain ⟨g₀, ⟨h1, h2⟩, huniq⟩ := hN.2 c ((hXY c).mpr hc)
    have hcr : ∀ g ∈ N, (epCross (ep2A α β Y e e' y₁) (ep2B α β Y e e' y₁) {c} g ↔
        epCross α β {c} g) := by
      intro g hg
      have a := hedge g hg
      have b := hAB g a.1 (fun h' => h'.elim a.2.1 a.2.2.2.2)
      unfold epCross; rw [b.1, b.2]
    exact ⟨g₀, ⟨h1, (hcr g₀ h1).mp h2⟩, fun g hg => huniq g ⟨hg.1, (hcr g hg.1).mpr hg.2⟩⟩
  have hXeven : X.card % 2 = 0 := by
    have hc2 : (epCut α β X).card = 2 := by
      have : epCut α β X = {e, e'} := by
        ext g; rw [mem_epCut, hcut, Finset.mem_insert, Finset.mem_singleton]
      rw [this, Finset.card_pair hee']
    rw [← epD_cut_parity α β L h X hXL, hc2]
  intro p hp
  obtain ⟨hp0, hpS, hp1, hpb⟩ := hp
  -- a local matching avoiding `e` has an alternating flip set
  have hA : ∀ N, p N ≠ 0 → e ∉ N → 1 ≤ epAltNum α β X N := by
    intro N hN heN
    have hNLM := hpS N hN
    have hNnl : ∀ g ∈ N, α g ≠ β g := by
      intro g hg
      rcases h.1 g with h' | h'
      · exact h'.2.2
      · exact absurd (epD_live_of_mem_lm h X hXL hNLM g hg).1 h'.1
    -- `e' ∉ N` by parity
    have he'N : e' ∉ N := by
      intro he'
      have hd := ep_double_count α β N hNnl X
      have h1 : ∀ c ∈ X, (N.filter (epCross α β {c})).card = 1 :=
        fun c hcX => (ep_unique_iff_card N _).mp (hNLM.2 c hcX)
      rw [Finset.sum_congr rfl h1, Finset.sum_const, smul_eq_mul, mul_one] at hd
      have hf : N.filter (epCross α β X) = {e'} := by
        ext g
        rw [Finset.mem_filter, Finset.mem_singleton, hcut]
        constructor
        · rintro ⟨hg, hg' | hg'⟩
          · exact absurd (hg' ▸ hg) heN
          · exact hg'
        · intro hg; exact ⟨hg ▸ he', Or.inr hg⟩
      rw [hf, Finset.card_singleton] at hd
      omega
    -- all edges of `N` lie inside `X`
    have hNin : ∀ g ∈ N, α g ∈ X ∧ β g ∈ X := by
      intro g hg
      have hnc : ¬epCross α β X g := by
        rw [hcut]; rintro (h' | h')
        · exact heN (h' ▸ hg)
        · exact he'N (h' ▸ hg)
      unfold epCross at hnc
      rcases hNLM.1 g hg with h' | h'
      · exact ⟨h', by by_contra h''; exact hnc (Or.inl ⟨h', h''⟩)⟩
      · exact ⟨by by_contra h''; exact hnc (Or.inr ⟨h'', h'⟩), h'⟩
    -- one of the two matchings of the contraction differs from `N`
    obtain ⟨N₂, hN₂, hne₂⟩ : ∃ N₂, (N₂ ∈ epLM α β X ∧ ∀ g ∈ N₂, α g ∈ X ∧ β g ∈ X) ∧ N ≠ N₂ := by
      by_cases hNM : N = M₁
      · exact ⟨M₂, hback M₂ hM₂ heM₂, fun h' => hM12 (hNM.symm.trans h')⟩
      · exact ⟨M₁, hback M₁ hM₁ heM₁, hNM⟩
    refine ep_two_LM_altNum' α β X hnl hN₂.1 hne₂ ?_
    intro g hg
    rcases Finset.mem_symmDiff.mp hg with ⟨h', -⟩ | ⟨h', -⟩
    · exact hNin g h'
    · exact hN₂.2 g h'
  have heX : α e ∈ X ∨ β e ∈ X := by
    have := (hcut e).mpr (Or.inl rfl)
    unfold epCross at this; tauto
  have h13 := hpb e heX
  have hsum : ∑ N, p N * (1 - epInd N e) = 2 / 3 := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hp1, h13]; norm_num
  have hle : ∑ N, p N * (1 - epInd N e) ≤ ∑ N, p N * (epAltNum α β X N : ℝ) := by
    refine Finset.sum_le_sum fun N _ => ?_
    by_cases hN : p N = 0
    · rw [hN, zero_mul, zero_mul]
    · refine mul_le_mul_of_nonneg_left ?_ (hp0 N)
      by_cases he : e ∈ N
      · have : epInd N e = 1 := by unfold epInd; rw [if_pos he]
        rw [this, sub_self]; exact Nat.cast_nonneg _
      · have : epInd N e = 0 := by unfold epInd; rw [if_neg he]
        rw [this, sub_zero]
        exact_mod_cast hA N hN he
  linarith

set_option maxHeartbeats 1600000 in
open Classical in
/-- Contracting a side of a 3-edge-cut does not increase the number of perfect matchings. -/
lemma ep3_m_le {W E : Type*} [Fintype E] (α β : E → W) (L X Y : Finset W)
    (x₀ x₁ y₀ y₁ : W) (h : EpCubicD α β L) (hb : EpBridgeless α β L) (hXL : X ⊆ L)
    (hY : ∀ w, w ∈ Y ↔ w ∈ L ∧ w ∉ X) (hx₀ : x₀ ∈ X) (hx₁ : x₁ ∈ X) (hx : x₁ ≠ x₀)
    (hy₀ : y₀ ∈ Y) (h3 : (epCut α β X).card = 3) :
    epM (epConA α β Y y₀ y₁) (epConB α β Y y₀ y₁) (epL' L Y y₀) ≤ epM α β L := by
  have hYL : Y ⊆ L := fun w hw => ((hY w).mp hw).1
  have hX : ∀ w, w ∈ X ↔ w ∈ L ∧ w ∉ Y := by
    intro w
    constructor
    · intro hw; exact ⟨hXL hw, fun h' => ((hY w).mp h').2 hw⟩
    · rintro ⟨h1, h2⟩; by_contra h'; exact h2 ((hY w).mpr ⟨h1, h'⟩)
  obtain ⟨hc₂, hb₂⟩ := epCon_cubic α β L X x₀ x₁ h hb hXL hx₀ hx₁ hx h3
  have hex : ∀ N₁, N₁ ∈ epPM (epConA α β Y y₀ y₁) (epConB α β Y y₀ y₁) (epL' L Y y₀) →
      ∃ N₂ f, N₂ ∈ epPM (epConA α β X x₀ x₁) (epConB α β X x₀ x₁) (epL' L X x₀) ∧
        f ∈ N₁ ∧ f ∈ N₂ ∧ epCross α β X f := by
    intro N₁ hN₁
    obtain ⟨f, ⟨hf1, hf2⟩, -⟩ := epCon_pm_cut α β L Y y₀ y₁ hy₀ hN₁
    rw [epD_cross_compl α β L X Y h hY] at hf2
    have hlive := epD_live_of_cross h X f hf2
    have hnin : ¬(α f ∈ X ∧ β f ∈ X) := by unfold epCross at hf2; tauto
    have hl : epConA α β X x₀ x₁ f ∈ epL' L X x₀ := by
      unfold epConA; rw [if_neg hnin]; exact epRho_mem_L' L X x₀ _ hlive.1
    obtain ⟨N₂, hN₂, hfN₂⟩ := epD_edge_in_pm _ _ _ hc₂ hb₂ f hl
    exact ⟨N₂, f, hN₂, hf1, hfN₂, hf2⟩
  choose c fc hc using hex
  unfold epM
  refine Finset.card_le_card_of_injOn
    (fun N₁ => if hN : N₁ ∈ epPM (epConA α β Y y₀ y₁) (epConB α β Y y₀ y₁) (epL' L Y y₀)
      then N₁ ∪ c N₁ hN else ∅) ?_ ?_
  · intro N₁ hN₁
    have hN := (mem_epPMs _ _ _ _).mp (Finset.mem_coe.mp hN₁)
    rw [Finset.mem_coe, mem_epPMs]
    simp only [dif_pos hN]
    obtain ⟨a1, a2, a3, a4⟩ := hc N₁ hN
    exact ep3_glue α β L X Y x₀ x₁ y₀ y₁ h hY hx₀ hy₀ hN a1 (fc N₁ hN) a2 a3 a4
  · intro N₁ hN₁ N₁' hN₁' heq
    have hN := (mem_epPMs _ _ _ _).mp (Finset.mem_coe.mp hN₁)
    have hN' := (mem_epPMs _ _ _ _).mp (Finset.mem_coe.mp hN₁')
    simp only [dif_pos hN, dif_pos hN'] at heq
    obtain ⟨a1, a2, a3, a4⟩ := hc N₁ hN
    obtain ⟨b1, b2, b3, b4⟩ := hc N₁' hN'
    have a4' := (epD_cross_compl α β L X Y h hY _).mpr a4
    have b4' := (epD_cross_compl α β L X Y h hY _).mpr b4
    rw [← ep3_glue_filter α β L Y X y₀ y₁ x₀ x₁ h hX hx₀ a1 hN (fc N₁ hN) a3 a2 a4',
      ← ep3_glue_filter α β L Y X y₀ y₁ x₀ x₁ h hX hx₀ b1 hN' (fc N₁' hN') b3 b2 b4',
      Finset.union_comm (c N₁ hN) N₁, Finset.union_comm (c N₁' hN') N₁', heq]

open Classical in
/-- In a cubic cyclically 4-edge-connected multigraph with at least six vertices there are at
least four perfect matchings. -/
lemma epD_cyc4_four {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (h : EpCubicD α β L) (h4 : EpCyc4 α β L) (h6 : 6 ≤ L.card) : 4 ≤ epM α β L := by
  obtain ⟨v, hv⟩ : L.Nonempty := Finset.card_pos.mp (by omega)
  have hcard := h.2 v hv
  obtain ⟨g₁, hg₁, g₂, hg₂, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < (epCut α β {v}).card)
  rw [mem_epCut] at hg₁ hg₂
  obtain ⟨A₁, A₂, hA₁, hA₂, hA, a1, a2⟩ := epD_lemma22 α β L h h4 h6 g₁
    (epD_live_of_cross h _ g₁ hg₁).1
  obtain ⟨B₁, B₂, hB₁, hB₂, hB, b1, b2⟩ := epD_lemma22 α β L h h4 h6 g₂
    (epD_live_of_cross h _ g₂ hg₂).1
  have hdiff : ∀ A B, A ∈ epPM α β L → g₁ ∈ A → g₂ ∈ B → A ≠ B := by
    intro A B hAm ha hb' heq
    exact hne ((hAm.2 v hv).unique ⟨ha, hg₁⟩ ⟨heq ▸ hb', hg₂⟩)
  unfold epM
  have hsub : ({A₁, A₂, B₁, B₂} : Finset (Finset E)) ⊆ epPMs α β L := by
    intro N hN
    simp only [Finset.mem_insert, Finset.mem_singleton] at hN
    rw [mem_epPMs]
    rcases hN with rfl | rfl | rfl | rfl <;> assumption
  refine le_trans ?_ (Finset.card_le_card hsub)
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hB]
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h' | h')
    · exact hdiff A₂ B₁ hA₂ a2 b1 h'
    · exact hdiff A₂ B₂ hA₂ a2 b2 h'
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h' | h' | h')
    · exact hA h'
    · exact hdiff A₁ B₁ hA₁ a1 b1 h'
    · exact hdiff A₁ B₂ hA₁ a1 b2 h'

set_option maxHeartbeats 1600000 in
open Classical in
/-- A cubic bridgeless multigraph with a 2-edge-cut has at least four perfect matchings. -/
lemma ep2_four {W E : Type*} [Fintype E] (α β : E → W) (L X Y : Finset W) (e e' : E)
    (x₁ y₁ : W) (h : EpCubicD α β L) (hb : EpBridgeless α β L) (hXL : X ⊆ L)
    (hY : ∀ w, w ∈ Y ↔ w ∈ L ∧ w ∉ X) (hx₁ : x₁ ∈ X) (hy₁ : y₁ ∈ Y) (hee' : e ≠ e')
    (hcut : ∀ g, epCross α β X g ↔ g = e ∨ g = e') : 4 ≤ epM α β L := by
  have hYL : Y ⊆ L := fun w hw => ((hY w).mp hw).1
  have hX : ∀ w, w ∈ X ↔ w ∈ L ∧ w ∉ Y := by
    intro w
    constructor
    · intro hw; exact ⟨hXL hw, fun h' => ((hY w).mp h').2 hw⟩
    · rintro ⟨h1, h2⟩; by_contra h'; exact h2 ((hY w).mpr ⟨h1, h'⟩)
  have hcutY := ep2_cut_compl α β L X Y e e' h hY hcut
  obtain ⟨hcX, hbX⟩ := ep2_cubic α β L Y e e' y₁ h hb hYL hy₁ hee' hcutY
  obtain ⟨hcY, hbY⟩ := ep2_cubic α β L X e e' x₁ h hb hXL hx₁ hee' hcut
  have hliveX : ep2A α β Y e e' y₁ e ∈ L \ Y := by
    obtain ⟨a1, a2, -, -⟩ := ep_cut_insert_card α β L Y h hb hYL e e' hee' hcutY e (Or.inl rfl)
    have : ep2A α β Y e e' y₁ e = epOut α β Y e := by unfold ep2A; rw [if_pos rfl]
    rw [this]; exact Finset.mem_sdiff.mpr ⟨a1, a2⟩
  have hliveY : ep2A α β X e e' x₁ e ∈ L \ X := by
    obtain ⟨a1, a2, -, -⟩ := ep_cut_insert_card α β L X h hb hXL e e' hee' hcut e (Or.inl rfl)
    have : ep2A α β X e e' x₁ e = epOut α β X e := by unfold ep2A; rw [if_pos rfl]
    rw [this]; exact Finset.mem_sdiff.mpr ⟨a1, a2⟩
  obtain ⟨A₁, A₂, hA₁, hA₂, hA, a1, a2⟩ := epD_two_pm_avoiding _ _ _ hcX hbX e hliveX
  obtain ⟨B₁, B₂, hB₁, hB₂, hB, b1, b2⟩ := epD_two_pm_avoiding _ _ _ hcY hbY e hliveY
  have hAm : ∀ N ∈ ({A₁, A₂} : Finset (Finset E)),
      N ∈ epPM (ep2A α β Y e e' y₁) (ep2B α β Y e e' y₁) (L \ Y) ∧ e ∉ N := by
    intro N hN
    rw [Finset.mem_insert, Finset.mem_singleton] at hN
    rcases hN with rfl | rfl
    · exact ⟨hA₁, a1⟩
    · exact ⟨hA₂, a2⟩
  have hBm : ∀ N ∈ ({B₁, B₂} : Finset (Finset E)),
      N ∈ epPM (ep2A α β X e e' x₁) (ep2B α β X e e' x₁) (L \ X) ∧ e ∉ N := by
    intro N hN
    rw [Finset.mem_insert, Finset.mem_singleton] at hN
    rcases hN with rfl | rfl
    · exact ⟨hB₁, b1⟩
    · exact ⟨hB₂, b2⟩
  have hcard : (({A₁, A₂} : Finset (Finset E)) ×ˢ ({B₁, B₂} : Finset (Finset E))).card = 4 := by
    rw [Finset.card_product, Finset.card_pair hA, Finset.card_pair hB]
  unfold epM
  rw [← hcard]
  refine Finset.card_le_card_of_injOn (fun p => ep2Glue e e' p.1 p.2) ?_ ?_
  · rintro ⟨N₁, N₂⟩ hp
    rw [Finset.mem_coe, Finset.mem_product] at hp
    obtain ⟨c1, c2⟩ := hAm N₁ hp.1
    obtain ⟨d1, d2⟩ := hBm N₂ hp.2
    rw [Finset.mem_coe, mem_epPMs]
    exact ep2_glue α β L X Y e e' x₁ y₁ h hb hXL hY hee' hcut N₁ N₂ c1 d1
      ⟨fun h' => absurd h' c2, fun h' => absurd h' d2⟩
  · rintro ⟨N₁, N₂⟩ hp ⟨N₁', N₂'⟩ hp' heq
    rw [Finset.mem_coe, Finset.mem_product] at hp hp'
    obtain ⟨c1, c2⟩ := hAm N₁ hp.1
    obtain ⟨d1, d2⟩ := hBm N₂ hp.2
    obtain ⟨c1', c2'⟩ := hAm N₁' hp'.1
    obtain ⟨d1', d2'⟩ := hBm N₂' hp'.2
    dsimp only at heq
    have i1 : e ∈ N₁ ↔ e ∈ N₂ := ⟨fun h' => absurd h' c2, fun h' => absurd h' d2⟩
    have i2 : e ∈ N₁' ↔ e ∈ N₂' := ⟨fun h' => absurd h' c2', fun h' => absurd h' d2'⟩
    have e2 : N₂ = N₂' := by
      rw [← ep2_glue_filter α β L X Y e e' x₁ y₁ h hY hee' hcut N₁ N₂ c1 d1 i1,
        ← ep2_glue_filter α β L X Y e e' x₁ y₁ h hY hee' hcut N₁' N₂' c1' d1' i2, heq]
    have e1 : N₁ = N₁' := by
      rw [← ep2_glue_filter α β L Y X e e' y₁ x₁ h hX hee' hcutY N₂ N₁ d1 c1 i1.symm,
        ← ep2_glue_filter α β L Y X e e' y₁ x₁ h hX hee' hcutY N₂' N₁' d1' c1' i2.symm,
        ← ep2Glue_comm e e' N₁ N₂ i1, ← ep2Glue_comm e e' N₁' N₂' i2, heq]
    rw [e1, e2]

open Classical in
/-- A cubic bridgeless connected multigraph is cyclically 4-edge-connected, or has a 2-edge-cut,
or has a 3-edge-cut with at least three vertices on each side. -/
lemma epD_cut_trichotomy {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (h : EpCubicD α β L) (hb : EpBridgeless α β L) (hconn : EpConnected α β L) :
    EpCyc4 α β L ∨
      (∃ X e e', X ⊆ L ∧ X.Nonempty ∧ X ≠ L ∧ e ≠ e' ∧
        ∀ g, epCross α β X g ↔ g = e ∨ g = e') ∨
      (∃ X, X ⊆ L ∧ (epCut α β X).card = 3 ∧ 3 ≤ X.card ∧ 3 ≤ (L \ X).card) := by
  by_cases h4 : EpCyc4 α β L
  · exact Or.inl h4
  · right
    unfold EpCyc4 at h4
    rw [not_and_or] at h4
    rcases h4 with h4 | h4
    · left
      push Not at h4
      obtain ⟨T, hTL, hTne, hTL', hlt⟩ := h4
      have h0 : (epCut α β T).card ≠ 0 := fun h' =>
        hconn T hTL hTne hTL' (Finset.card_eq_zero.mp h')
      have h1 := hb T hTL
      have h2 : (epCut α β T).card = 2 := by omega
      obtain ⟨e, e', hee', hcut⟩ := Finset.card_eq_two.mp h2
      refine ⟨T, e, e', hTL, hTne, hTL', hee', fun g => ?_⟩
      rw [← mem_epCut, hcut, Finset.mem_insert, Finset.mem_singleton]
    · right
      push Not at h4
      obtain ⟨T, hTL, h3, hT1, hT1'⟩ := h4
      have hpar := epD_cut_parity α β L h T hTL
      have hparL := epD_cut_parity α β L h L (Finset.Subset.refl L)
      have hcutL : epCut α β L = ∅ := by
        ext g
        rw [mem_epCut]
        simp only [Finset.notMem_empty, iff_false]
        intro hc
        have := epD_live_of_cross h L g hc
        unfold epCross at hc; tauto
      rw [hcutL, Finset.card_empty] at hparL
      rw [h3] at hpar
      have hle := Finset.card_le_card hTL
      have hsd : (L \ T).card = L.card - T.card := Finset.card_sdiff_of_subset hTL
      exact ⟨T, hTL, h3, by omega, by omega⟩

lemma ep_cross_two_ends {W E : Type*} (α β : E → W) (g : E) (p q : W) (hpq : p ≠ q)
    (hp : epCross α β {p} g) (hq : epCross α β {q} g) :
    α g ≠ β g ∧ ∀ w, epCross α β {w} g ↔ w = p ∨ w = q := by
  have hne : α g ≠ β g := by
    intro h'; rw [epCross_singleton, h'] at hp; tauto
  refine ⟨hne, fun w => ?_⟩
  rw [ep_cross_ends α β g hne w]
  have h1 := (ep_cross_ends α β g hne p).mp hp
  have h2 := (ep_cross_ends α β g hne q).mp hq
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hpq
  · rw [← h1, ← h2]
  · rw [← h1, ← h2]; tauto
  · exact absurd (h1.trans h2.symm) hpq

set_option maxHeartbeats 3200000 in
open Classical in
/-- A cubic bridgeless multigraph on four vertices with two parallel edges has at least four
perfect matchings. -/
lemma epD_four_of_parallel {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (h : EpCubicD α β L) (hb : EpBridgeless α β L) (hL4 : L.card = 4) (v z : W) (hvz : v ≠ z)
    (f₂ f₃ : E) (hf : f₂ ≠ f₃) (hv2 : epCross α β {v} f₂) (hz2 : epCross α β {z} f₂)
    (hv3 : epCross α β {v} f₃) (hz3 : epCross α β {z} f₃) : 4 ≤ epM α β L := by
  obtain ⟨hnl2, H2⟩ := ep_cross_two_ends α β f₂ v z hvz hv2 hz2
  obtain ⟨hnl3, H3⟩ := ep_cross_two_ends α β f₃ v z hvz hv3 hz3
  have hlive2 := epD_live_of_cross h {v} f₂ hv2
  have hvL : v ∈ L := by
    rcases (ep_cross_ends α β f₂ hnl2 v).mp hv2 with h' | h'
    · rw [h']; exact hlive2.1
    · rw [h']; exact hlive2.2.1
  have hzL : z ∈ L := by
    rcases (ep_cross_ends α β f₂ hnl2 z).mp hz2 with h' | h'
    · rw [h']; exact hlive2.1
    · rw [h']; exact hlive2.2.1
  -- the other two vertices
  have hc2 : ((L.erase v).erase z).card = 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hvz, hzL⟩),
      Finset.card_erase_of_mem hvL, hL4]
  obtain ⟨x, y, hxy, hxyset⟩ := Finset.card_eq_two.mp hc2
  have hmemL : ∀ w, w ∈ L → w = v ∨ w = z ∨ w = x ∨ w = y := by
    intro w hw
    by_cases h1 : w = v
    · exact Or.inl h1
    · by_cases h2 : w = z
      · exact Or.inr (Or.inl h2)
      · have : w ∈ (L.erase v).erase z :=
          Finset.mem_erase.mpr ⟨h2, Finset.mem_erase.mpr ⟨h1, hw⟩⟩
        rw [hxyset, Finset.mem_insert, Finset.mem_singleton] at this
        exact Or.inr (Or.inr this)
  have hx : x ∈ (L.erase v).erase z := by rw [hxyset]; exact Finset.mem_insert_self _ _
  have hy : y ∈ (L.erase v).erase z := by
    rw [hxyset]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hxz : x ≠ z := Finset.ne_of_mem_erase hx
  have hxv : x ≠ v := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hx)
  have hxL : x ∈ L := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)
  have hyz : y ≠ z := Finset.ne_of_mem_erase hy
  have hyv : y ≠ v := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hy)
  have hyL : y ∈ L := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy)
  -- a perfect matching through `f₂`
  obtain ⟨N, hN, hf2N⟩ := epD_edge_in_pm α β L h hb f₂ hlive2.1
  have hf3N : f₃ ∉ N := fun h' => hf ((hN.2 v hvL).unique ⟨hf2N, hv2⟩ ⟨h', hv3⟩)
  obtain ⟨p, ⟨hpN, hpx⟩, -⟩ := hN.2 x hxL
  have hpnl := hN.1 p hpN
  obtain ⟨u, hux, huend, Hp⟩ := ep_other_end α β p hpnl x hpx
  have hplive := epD_live_of_mem_pm h hN p hpN
  have huL : u ∈ L := by
    rcases huend with h' | h'
    · rw [h']; exact hplive.1
    · rw [h']; exact hplive.2
  have hpf2 : p ≠ f₂ := by
    intro h'; rw [h'] at hpx
    rcases (H2 x).mp hpx with h'' | h''
    · exact hxv h''
    · exact hxz h''
  have huy : u = y := by
    rcases hmemL u huL with h' | h' | h' | h'
    · exfalso
      exact hpf2 ((hN.2 v hvL).unique ⟨hpN, (Hp v).mpr (Or.inr h'.symm)⟩ ⟨hf2N, hv2⟩)
    · exfalso
      exact hpf2 ((hN.2 z hzL).unique ⟨hpN, (Hp z).mpr (Or.inr h'.symm)⟩ ⟨hf2N, hz2⟩)
    · exact absurd h' hux
    · exact h'
  rw [huy] at Hp
  have hpy : epCross α β {y} p := (Hp y).mpr (Or.inr rfl)
  -- a second edge joining `x` and `y`
  obtain ⟨p', hp'p, hp'x, hp'y⟩ : ∃ p', p' ≠ p ∧ epCross α β {x} p' ∧ epCross α β {y} p' := by
    by_contra hcon
    push Not at hcon
    -- edges at `v` and `z` other than `f₂`, `f₃`
    have hRV : ((epCut α β {v}).erase f₂ |>.erase f₃).card = 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hf, (mem_epCut _ _ _ _).mpr hv3⟩),
        Finset.card_erase_of_mem ((mem_epCut _ _ _ _).mpr hv2), h.2 v hvL]
    have hRZ : ((epCut α β {z}).erase f₂ |>.erase f₃).card = 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hf, (mem_epCut _ _ _ _).mpr hz3⟩),
        Finset.card_erase_of_mem ((mem_epCut _ _ _ _).mpr hz2), h.2 z hzL]
    -- an edge at `c ∈ {x, y}` other than `p` goes to `v` or `z`, or to the other of `x`, `y`
    have hother : ∀ c c', (c = x ∧ c' = y) ∨ (c = y ∧ c' = x) → ∀ q, epCross α β {c} q →
        q ≠ p → (q ∈ ((epCut α β {v}).erase f₂ |>.erase f₃) ∨
          q ∈ ((epCut α β {z}).erase f₂ |>.erase f₃)) := by
      intro c c' hcc q hqc hqp
      have hcL : c ∈ L := by rcases hcc with ⟨h', -⟩ | ⟨h', -⟩ <;> rw [h'] <;> assumption
      have hcv : c ≠ v := by rcases hcc with ⟨h', -⟩ | ⟨h', -⟩ <;> rw [h'] <;> assumption
      have hcz : c ≠ z := by rcases hcc with ⟨h', -⟩ | ⟨h', -⟩ <;> rw [h'] <;> assumption
      have hqlive := epD_live_of_cross h {c} q hqc
      obtain ⟨u', hu'c, hu'end, Hq⟩ := ep_other_end α β q hqlive.2.2 c hqc
      have hu'L : u' ∈ L := by
        rcases hu'end with h' | h'
        · rw [h']; exact hqlive.1
        · rw [h']; exact hqlive.2.1
      have hq2 : q ≠ f₂ := by
        intro h'; rw [h'] at hqc
        rcases (H2 c).mp hqc with h'' | h''
        · exact hcv h''
        · exact hcz h''
      have hq3 : q ≠ f₃ := by
        intro h'; rw [h'] at hqc
        rcases (H3 c).mp hqc with h'' | h''
        · exact hcv h''
        · exact hcz h''
      have hqxy : ¬(epCross α β {x} q ∧ epCross α β {y} q) := fun h' =>
        hqp (by by_contra hne'; exact hcon q hne' h'.1 h'.2)
      rcases hmemL u' hu'L with h' | h' | h' | h'
      · left
        exact Finset.mem_erase.mpr ⟨hq3, Finset.mem_erase.mpr ⟨hq2,
          (mem_epCut _ _ _ _).mpr ((Hq v).mpr (Or.inr h'.symm))⟩⟩
      · right
        exact Finset.mem_erase.mpr ⟨hq3, Finset.mem_erase.mpr ⟨hq2,
          (mem_epCut _ _ _ _).mpr ((Hq z).mpr (Or.inr h'.symm))⟩⟩
      · exfalso
        rcases hcc with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact hu'c (h'.trans h1.symm)
        · exact hqxy ⟨(Hq x).mpr (Or.inr h'.symm), h1 ▸ hqc⟩
      · exfalso
        rcases hcc with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact hqxy ⟨h1 ▸ hqc, (Hq y).mpr (Or.inr h'.symm)⟩
        · exact hu'c (h'.trans h1.symm)
    have hQx : (epCut α β {x}).erase p ⊆ ((epCut α β {v}).erase f₂ |>.erase f₃) ∪
        ((epCut α β {z}).erase f₂ |>.erase f₃) := by
      intro q hq
      rw [Finset.mem_union]
      exact hother x y (Or.inl ⟨rfl, rfl⟩) q ((mem_epCut _ _ _ _).mp (Finset.mem_of_mem_erase hq))
        (Finset.ne_of_mem_erase hq)
    have hQxc : ((epCut α β {x}).erase p).card = 2 := by
      rw [Finset.card_erase_of_mem ((mem_epCut _ _ _ _).mpr hpx), h.2 x hxL]
    have hUc := Finset.card_union_le ((epCut α β {v}).erase f₂ |>.erase f₃)
      ((epCut α β {z}).erase f₂ |>.erase f₃)
    have hQeq : (epCut α β {x}).erase p = ((epCut α β {v}).erase f₂ |>.erase f₃) ∪
        ((epCut α β {z}).erase f₂ |>.erase f₃) :=
      Finset.eq_of_subset_of_card_le hQx (by omega)
    -- then `y` has only the edge `p`
    have hycut : epCut α β {y} ⊆ {p} := by
      intro s hs
      rw [Finset.mem_singleton]
      by_contra hsp
      have hsc := (mem_epCut _ _ _ _).mp hs
      have := hother y x (Or.inr ⟨rfl, rfl⟩) s hsc hsp
      rw [← Finset.mem_union, ← hQeq] at this
      have hsx := (mem_epCut _ _ _ _).mp (Finset.mem_of_mem_erase this)
      exact hcon s hsp hsx hsc
    have := Finset.card_le_card hycut
    rw [h.2 y hyL, Finset.card_singleton] at this
    omega
  obtain ⟨-, Hp'⟩ := ep_cross_two_ends α β p' x y hxy hp'x hp'y
  have hp'live := epD_live_of_cross h {x} p' hp'x
  have hp'N : p' ∉ N := fun h' => hp'p ((hN.2 x hxL).unique ⟨h', hp'x⟩ ⟨hpN, hpx⟩)
  have hparp : ∀ w, epCross α β {w} p ↔ epCross α β {w} p' := fun w => by rw [Hp, Hp']
  have hparf : ∀ w, epCross α β {w} f₂ ↔ epCross α β {w} f₃ := fun w => by rw [H2, H3]
  have hlive3 := epD_live_of_cross h {v} f₃ hv3
  have hp'f2 : p' ≠ f₂ := by
    intro h'; rw [h'] at hp'x
    rcases (H2 x).mp hp'x with h'' | h''
    · exact hxv h''
    · exact hxz h''
  have hpf3 : p ≠ f₃ := by
    intro h'; rw [h'] at hpx
    rcases (H3 x).mp hpx with h'' | h''
    · exact hxv h''
    · exact hxz h''
  have hp'f3 : p' ≠ f₃ := by
    intro h'; rw [h'] at hp'x
    rcases (H3 x).mp hp'x with h'' | h''
    · exact hxv h''
    · exact hxz h''
  -- exchanging parallel edges keeps perfect matchings
  have hflip : ∀ (M : Finset E) (a b : E), M ∈ epPM α β L → a ∈ M → b ∉ M →
      (∀ w, epCross α β {w} a ↔ epCross α β {w} b) → α b ∈ L ∧ β b ∈ L → α b ≠ β b →
      symmDiff M {a, b} ∈ epPM α β L := by
    intro M a b hM ha hb' hpar hbL hbnl
    have hLM : M ∈ epLM α β L := ⟨fun g hg => Or.inl (epD_live_of_mem_pm h hM g hg).1, hM.2⟩
    have := ep_parallel_flip α β L hLM a b ha hb' hpar hbL
    refine ⟨fun g hg => ?_, this.2⟩
    rcases Finset.mem_symmDiff.mp hg with ⟨h', -⟩ | ⟨h', -⟩
    · exact hM.1 g h'
    · rcases Finset.mem_insert.mp h' with h'' | h''
      · rw [h'']; exact hM.1 a ha
      · rw [Finset.mem_singleton.mp h'']; exact hbnl
  have hN₁ := hflip N p p' hN hpN hp'N hparp ⟨hp'live.1, hp'live.2.1⟩ hp'live.2.2
  have hN₂ := hflip N f₂ f₃ hN hf2N hf3N hparf ⟨hlive3.1, hlive3.2.1⟩ hnl3
  have hf2N₁ : f₂ ∈ symmDiff N {p, p'} := Finset.mem_symmDiff.mpr (Or.inl ⟨hf2N, by
    simp only [Finset.mem_insert, Finset.mem_singleton]; rintro (h' | h')
    · exact hpf2 h'.symm
    · exact hp'f2 h'.symm⟩)
  have hf3N₁ : f₃ ∉ symmDiff N {p, p'} := by
    rw [Finset.mem_symmDiff]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (⟨h', -⟩ | ⟨h' | h', -⟩)
    · exact hf3N h'
    · exact hpf3 h'.symm
    · exact hp'f3 h'.symm
  have hN₃ := hflip _ f₂ f₃ hN₁ hf2N₁ hf3N₁ hparf ⟨hlive3.1, hlive3.2.1⟩ hnl3
  -- membership of `f₂` and `p` separates the four matchings
  have m1 : p ∉ symmDiff N {p, p'} := by
    rw [Finset.mem_symmDiff]; simp [hpN]
  have m2 : p ∈ symmDiff N {f₂, f₃} := Finset.mem_symmDiff.mpr (Or.inl ⟨hpN, by
    simp only [Finset.mem_insert, Finset.mem_singleton]; rintro (h' | h')
    · exact hpf2 h'
    · exact hpf3 h'⟩)
  have m3 : f₂ ∉ symmDiff N {f₂, f₃} := by
    rw [Finset.mem_symmDiff]; simp [hf2N]
  have m4 : f₂ ∉ symmDiff (symmDiff N {p, p'}) {f₂, f₃} := by
    rw [Finset.mem_symmDiff]; simp [hf2N₁]
  have m5 : p ∉ symmDiff (symmDiff N {p, p'}) {f₂, f₃} := by
    rw [Finset.mem_symmDiff]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (⟨h', -⟩ | ⟨h' | h', -⟩)
    · exact m1 h'
    · exact hpf2 h'
    · exact hpf3 h'
  unfold epM
  have hsub : ({N, symmDiff N {p, p'}, symmDiff N {f₂, f₃},
      symmDiff (symmDiff N {p, p'}) {f₂, f₃}} : Finset (Finset E)) ⊆ epPMs α β L := by
    intro M hM
    simp only [Finset.mem_insert, Finset.mem_singleton] at hM
    rw [mem_epPMs]
    rcases hM with rfl | rfl | rfl | rfl <;> assumption
  refine le_trans ?_ (Finset.card_le_card hsub)
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair]
  · intro h'; exact m5 (h' ▸ m2)
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h' | h')
    · exact m3 (h' ▸ hf2N₁)
    · exact m4 (h' ▸ hf2N₁)
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h' | h' | h')
    · exact m1 (h' ▸ hpN)
    · exact m3 (h' ▸ hf2N)
    · exact m4 (h' ▸ hf2N)

lemma epCon_connected {W E : Type*} [Fintype E] (α β : E → W) (L X : Finset W) (x₀ x₁ : W)
    (hXL : X ⊆ L) (hx₀ : x₀ ∈ X) (hconn : EpConnected α β L) :
    EpConnected (epConA α β X x₀ x₁) (epConB α β X x₀ x₁) (epL' L X x₀) := by
  classical
  intro T' hT' hne hneL
  rw [epCon_cut α β L X x₀ x₁ hx₀ T' hT']
  refine hconn _ (epLift_subset L X x₀ hXL hx₀ T' hT') ?_ ?_
  · obtain ⟨w, hw⟩ := hne
    unfold epLift
    split_ifs
    · exact ⟨w, Finset.mem_union_left _ hw⟩
    · exact ⟨w, hw⟩
  · intro hL
    unfold epLift at hL
    by_cases hx : x₀ ∈ T'
    · rw [if_pos hx] at hL
      apply hneL
      refine Finset.Subset.antisymm hT' ?_
      intro w hw
      unfold epL' at hw
      rw [Finset.mem_insert, Finset.mem_sdiff] at hw
      rcases hw with rfl | ⟨h1, h2⟩
      · exact hx
      · have : w ∈ T' ∪ X := hL ▸ h1
        exact (Finset.mem_union.mp this).resolve_right h2
    · rw [if_neg hx] at hL
      exact hx (hL ▸ hXL hx₀)

set_option maxHeartbeats 3200000 in
open Classical in
/-- A cubic bridgeless multigraph with a 3-edge-cut both of whose sides have three vertices has
at least four perfect matchings. -/
lemma ep33_four {W E : Type*} [Fintype E] (α β : E → W) (L X Y : Finset W)
    (x₀ x₁ y₀ y₁ : W) (h : EpCubicD α β L) (hb : EpBridgeless α β L) (hXL : X ⊆ L)
    (hY : ∀ w, w ∈ Y ↔ w ∈ L ∧ w ∉ X) (hx₀ : x₀ ∈ X) (hx₁ : x₁ ∈ X) (hx : x₁ ≠ x₀)
    (hy₀ : y₀ ∈ Y) (hy₁ : y₁ ∈ Y) (hy : y₁ ≠ y₀) (h3 : (epCut α β X).card = 3)
    (hX3 : X.card = 3) (hY3 : Y.card = 3) : 4 ≤ epM α β L := by
  have hYL : Y ⊆ L := fun w hw => ((hY w).mp hw).1
  have hX : ∀ w, w ∈ X ↔ w ∈ L ∧ w ∉ Y := by
    intro w
    constructor
    · intro hw; exact ⟨hXL hw, fun h' => ((hY w).mp h').2 hw⟩
    · rintro ⟨h1, h2⟩; by_contra h'; exact h2 ((hY w).mpr ⟨h1, h'⟩)
  have hcomp := epD_cross_compl α β L X Y h hY
  have h3Y : (epCut α β Y).card = 3 := by
    have : epCut α β Y = epCut α β X := by
      ext g; rw [mem_epCut, mem_epCut]; exact hcomp g
    rw [this]; exact h3
  obtain ⟨hc₁, hb₁⟩ := epCon_cubic α β L Y y₀ y₁ h hb hYL hy₀ hy₁ hy h3Y
  obtain ⟨hc₂, hb₂⟩ := epCon_cubic α β L X x₀ x₁ h hb hXL hx₀ hx₁ hx h3
  by_cases m1 : 4 ≤ epM (epConA α β Y y₀ y₁) (epConB α β Y y₀ y₁) (epL' L Y y₀)
  · exact m1.trans (ep3_m_le α β L X Y x₀ x₁ y₀ y₁ h hb hXL hY hx₀ hx₁ hx hy₀ h3)
  by_cases m2 : 4 ≤ epM (epConA α β X x₀ x₁) (epConB α β X x₀ x₁) (epL' L X x₀)
  · exact m2.trans (ep3_m_le α β L Y X y₀ y₁ x₀ x₁ h hb hYL hX hy₀ hy₁ hy hx₀ h3Y)
  have hLcard : L.card = 6 := by
    have : L = X ∪ Y := by
      ext w; rw [Finset.mem_union, hY]
      constructor
      · intro hw; by_cases h' : w ∈ X
        · exact Or.inl h'
        · exact Or.inr ⟨hw, h'⟩
      · rintro (h' | h')
        · exact hXL h'
        · exact h'.1
    have hd : Disjoint X Y := by
      rw [Finset.disjoint_left]; intro w hw hw'; exact ((hY w).mp hw').2 hw
    rw [this, Finset.card_union_of_disjoint hd, hX3, hY3]
  -- cut edges have distinct ends on each side
  have hinj : ∀ (S S' : Finset W) (s₀ s₁ : W), S ⊆ L → s₀ ∈ S → S.card = 3 →
      (∀ w, w ∈ S' ↔ w ∈ L ∧ w ∉ S) →
      EpCubicD (epConA α β S s₀ s₁) (epConB α β S s₀ s₁) (epL' L S s₀) →
      EpBridgeless (epConA α β S s₀ s₁) (epConB α β S s₀ s₁) (epL' L S s₀) →
      ¬4 ≤ epM (epConA α β S s₀ s₁) (epConB α β S s₀ s₁) (epL' L S s₀) →
      ∀ c ∈ S', ∀ f f', epCross α β S f → epCross α β S f' → epCross α β {c} f →
        epCross α β {c} f' → f = f' := by
    intro S S' s₀ s₁ hSL hs₀ hS3 hS' hcS hbS hm c hc f f' hf hf' hfc hf'c
    by_contra hne
    apply hm
    have hcS' : c ∉ S := ((hS' c).mp hc).2
    have hc' : c ∈ epL' L S s₀ := by
      unfold epL'; exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨((hS' c).mp hc).1, hcS'⟩)
    have hs₀' : s₀ ∈ epL' L S s₀ := by unfold epL'; exact Finset.mem_insert_self _ _
    have hcs : s₀ ≠ c := fun h' => hcS' (h' ▸ hs₀)
    have e1 : ∀ g, epCross (epConA α β S s₀ s₁) (epConB α β S s₀ s₁) {s₀} g ↔
        epCross α β S g := fun g => by
      rw [epCon_cross α β L S s₀ s₁ hs₀ {s₀} (Finset.singleton_subset_iff.mpr hs₀'),
        epLift_singleton_t₀ S s₀ hs₀]
    have e2 : ∀ g, epCross (epConA α β S s₀ s₁) (epConB α β S s₀ s₁) {c} g ↔
        epCross α β {c} g := fun g => by
      rw [epCon_cross α β L S s₀ s₁ hs₀ {c} (Finset.singleton_subset_iff.mpr hc'),
        epLift_singleton_ne S s₀ c (Ne.symm hcs)]
    have hcard : (epL' L S s₀).card = 4 := by
      rw [epL'_card L S s₀ hSL hs₀, hLcard, hS3]
    exact epD_four_of_parallel _ _ _ hcS hbS hcard s₀ c hcs f f' hne ((e1 f).mpr hf)
      ((e2 f).mpr hfc) ((e1 f').mpr hf') ((e2 f').mpr hf'c)
  have hinjX := hinj Y X y₀ y₁ hYL hy₀ hY3 hX hc₁ hb₁ m1
  have hinjY := hinj X Y x₀ x₁ hXL hx₀ hX3 hY hc₂ hb₂ m2
  -- the cut is a perfect matching
  have hcutnl : ∀ g ∈ epCut α β X, α g ≠ β g := fun g hg =>
    (epD_live_of_cross h X g ((mem_epCut _ _ _ _).mp hg)).2.2
  have hside : ∀ S : Finset W, S.card = 3 → (∀ g, epCross α β S g ↔ epCross α β X g) →
      (∀ c ∈ S, ∀ f f', epCross α β X f → epCross α β X f' → epCross α β {c} f →
        epCross α β {c} f' → f = f') →
      ∀ c ∈ S, ∃! g, g ∈ epCut α β X ∧ epCross α β {c} g := by
    intro S hS3 hSX hinjS c hc
    have hd := ep_double_count α β (epCut α β X) hcutnl S
    have hf1 : (epCut α β X).filter (epCross α β S) = epCut α β X := by
      ext g
      rw [Finset.mem_filter]
      exact ⟨fun h' => h'.1, fun h' => ⟨h', (hSX g).mpr ((mem_epCut _ _ _ _).mp h')⟩⟩
    have hf2 : (epCut α β X).filter (fun e => α e ∈ S ∧ β e ∈ S) = ∅ := by
      ext g
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, mem_epCut]
      rintro ⟨hg, hin⟩
      have := (hSX g).mpr hg
      unfold epCross at this; tauto
    rw [hf1, hf2, Finset.card_empty, mul_zero, add_zero, h3] at hd
    have hle : ∀ c' ∈ S, ((epCut α β X).filter (epCross α β {c'})).card ≤ 1 := by
      intro c' hc'
      rw [Finset.card_le_one]
      intro a ha b hb'
      rw [Finset.mem_filter, mem_epCut] at ha hb'
      exact hinjS c' hc' a b ha.1 hb'.1 ha.2 hb'.2
    have hsum1 : ∑ _c' ∈ S, 1 = 3 := by simp [hS3]
    have := (Finset.sum_eq_sum_iff_of_le hle).mp (hd.trans hsum1.symm) c hc
    exact (ep_unique_iff_card _ _).mpr this
  have hM₀ : epCut α β X ∈ epPM α β L := by
    refine ⟨hcutnl, fun c hc => ?_⟩
    by_cases hcX : c ∈ X
    · exact hside X hX3 (fun _ => Iff.rfl) (fun c hc f f' hf hf' => hinjX c hc f f'
        ((hcomp f).mpr hf) ((hcomp f').mpr hf')) c hcX
    · exact hside Y hY3 hcomp hinjY c ((hY c).mpr ⟨hc, hcX⟩)
  -- a perfect matching through each cut edge, using no other cut edge
  have hP : ∀ f, epCross α β X f → ∃ P, P ∈ epPM α β L ∧ f ∈ P ∧
      ∀ f', epCross α β X f' → f' ∈ P → f' = f := by
    intro f hf
    have hlive := epD_live_of_cross h X f hf
    have hnX : ¬(α f ∈ X ∧ β f ∈ X) := by unfold epCross at hf; tauto
    have hfY := (hcomp f).mpr hf
    have hnY : ¬(α f ∈ Y ∧ β f ∈ Y) := by unfold epCross at hfY; tauto
    have hl₁ : epConA α β Y y₀ y₁ f ∈ epL' L Y y₀ := by
      unfold epConA; rw [if_neg hnY]; exact epRho_mem_L' L Y y₀ _ hlive.1
    have hl₂ : epConA α β X x₀ x₁ f ∈ epL' L X x₀ := by
      unfold epConA; rw [if_neg hnX]; exact epRho_mem_L' L X x₀ _ hlive.1
    obtain ⟨N₁, hN₁, hfN₁⟩ := epD_edge_in_pm _ _ _ hc₁ hb₁ f hl₁
    obtain ⟨N₂, hN₂, hfN₂⟩ := epD_edge_in_pm _ _ _ hc₂ hb₂ f hl₂
    refine ⟨N₁ ∪ N₂, ep3_glue α β L X Y x₀ x₁ y₀ y₁ h hY hx₀ hy₀ hN₁ hN₂ f hfN₁ hfN₂ hf,
      Finset.mem_union_left _ hfN₁, ?_⟩
    intro f' hf' hf'P
    rcases Finset.mem_union.mp hf'P with h' | h'
    · exact (epCon_pm_cut α β L Y y₀ y₁ hy₀ hN₁).unique ⟨h', (hcomp f').mpr hf'⟩ ⟨hfN₁, hfY⟩
    · exact (epCon_pm_cut α β L X x₀ x₁ hx₀ hN₂).unique ⟨h', hf'⟩ ⟨hfN₂, hf⟩
  obtain ⟨f₁, f₂, f₃, h12, h13, h23, hcutset⟩ := Finset.card_eq_three.mp h3
  have hfc : ∀ f, f = f₁ ∨ f = f₂ ∨ f = f₃ → epCross α β X f := by
    intro f hf
    rw [← mem_epCut, hcutset]
    simp only [Finset.mem_insert, Finset.mem_singleton]; exact hf
  obtain ⟨P₁, hP₁, a1, b1⟩ := hP f₁ (hfc f₁ (Or.inl rfl))
  obtain ⟨P₂, hP₂, a2, b2⟩ := hP f₂ (hfc f₂ (Or.inr (Or.inl rfl)))
  obtain ⟨P₃, hP₃, a3, b3⟩ := hP f₃ (hfc f₃ (Or.inr (Or.inr rfl)))
  have c1 := hfc f₁ (Or.inl rfl)
  have c2 := hfc f₂ (Or.inr (Or.inl rfl))
  have c3 := hfc f₃ (Or.inr (Or.inr rfl))
  have mem₀ : ∀ f, epCross α β X f → f ∈ epCut α β X := fun f hf => (mem_epCut _ _ _ _).mpr hf
  unfold epM
  have hsub : ({P₁, P₂, P₃, epCut α β X} : Finset (Finset E)) ⊆ epPMs α β L := by
    intro M hM
    simp only [Finset.mem_insert, Finset.mem_singleton] at hM
    rw [mem_epPMs]
    rcases hM with rfl | rfl | rfl | rfl <;> assumption
  refine le_trans ?_ (Finset.card_le_card hsub)
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair]
  · intro h'; exact h13 (b3 f₁ c1 (h' ▸ mem₀ f₁ c1))
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h' | h')
    · exact h23 (b3 f₂ c2 (h' ▸ a2))
    · exact h12 (b2 f₁ c1 (h' ▸ mem₀ f₁ c1))
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h' | h' | h')
    · exact h12 (b2 f₁ c1 (h' ▸ a1))
    · exact h13 (b3 f₁ c1 (h' ▸ a1))
    · exact h12.symm (b1 f₂ c2 (h' ▸ mem₀ f₂ c2))

set_option maxHeartbeats 1600000 in
open Classical in
/-- **A cubic bridgeless connected multigraph with at least six vertices has at least four
perfect matchings.** (Replaces the Edmonds–Lovász–Pulleyblank bound used in the paper.) -/
theorem epD_four {W E : Type*} [Fintype E] : ∀ (n : ℕ) (α β : E → W) (L : Finset W),
    L.card = n → EpCubicD α β L → EpBridgeless α β L → EpConnected α β L → 6 ≤ L.card →
    4 ≤ epM α β L := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro α β L hn h hb hconn h6
    rcases epD_cut_trichotomy α β L h hb hconn with h4 | ⟨X, e, e', hXL, hXne, hXL', hee', hcut⟩ |
      ⟨X, hXL, h3, hX3, hY3⟩
    · exact epD_cyc4_four α β L h h4 h6
    · obtain ⟨x₁, hx₁⟩ := hXne
      have hYne : (L \ X).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h'
        exact hXL' (Finset.Subset.antisymm hXL (Finset.sdiff_eq_empty_iff_subset.mp h'))
      obtain ⟨y₁, hy₁⟩ := hYne
      exact ep2_four α β L X (L \ X) e e' x₁ y₁ h hb hXL (fun w => Finset.mem_sdiff) hx₁ hy₁
        hee' hcut
    · have hY : ∀ w, w ∈ L \ X ↔ w ∈ L ∧ w ∉ X := fun w => Finset.mem_sdiff
      have hYL : L \ X ⊆ L := Finset.sdiff_subset
      have hXd : ∀ w, w ∈ X ↔ w ∈ L ∧ w ∉ L \ X := by
        intro w
        constructor
        · intro hw; exact ⟨hXL hw, fun h' => (Finset.mem_sdiff.mp h').2 hw⟩
        · rintro ⟨h1, h2⟩; by_contra h'; exact h2 (Finset.mem_sdiff.mpr ⟨h1, h'⟩)
      obtain ⟨x₀, hx₀, x₁, hx₁, hx⟩ := Finset.one_lt_card.mp (by omega : 1 < X.card)
      obtain ⟨y₀, hy₀, y₁, hy₁, hy⟩ := Finset.one_lt_card.mp (by omega : 1 < (L \ X).card)
      have hsd : (L \ X).card = L.card - X.card := Finset.card_sdiff_of_subset hXL
      have hle := Finset.card_le_card hXL
      have h3Y : (epCut α β (L \ X)).card = 3 := by
        have : epCut α β (L \ X) = epCut α β X := by
          ext g; rw [mem_epCut, mem_epCut]; exact epD_cross_compl α β L X (L \ X) h hY g
        rw [this]; exact h3
      by_cases hX5 : 5 ≤ X.card
      · -- contract `L \ X`: the contraction has `|X| + 1 ≥ 6` vertices
        obtain ⟨hc₁, hb₁⟩ := epCon_cubic α β L (L \ X) y₀ y₁ h hb hYL hy₀ hy₁ hy.symm h3Y
        have hcard := epL'_card L (L \ X) y₀ hYL hy₀
        have := ih _ (by omega) _ _ _ rfl hc₁ hb₁
          (epCon_connected α β L (L \ X) y₀ y₁ hYL hy₀ hconn) (by omega)
        exact this.trans (ep3_m_le α β L X (L \ X) x₀ x₁ y₀ y₁ h hb hXL hY hx₀ hx₁ hx.symm hy₀ h3)
      · by_cases hY5 : 5 ≤ (L \ X).card
        · obtain ⟨hc₂, hb₂⟩ := epCon_cubic α β L X x₀ x₁ h hb hXL hx₀ hx₁ hx.symm h3
          have hcard := epL'_card L X x₀ hXL hx₀
          have := ih _ (by omega) _ _ _ rfl hc₂ hb₂
            (epCon_connected α β L X x₀ x₁ hXL hx₀ hconn) (by omega)
          exact this.trans (ep3_m_le α β L (L \ X) X y₀ y₁ x₀ x₁ h hb hYL hXd hy₀ hy₁ hy.symm
            hx₀ h3Y)
        · -- both sides have exactly three vertices
          have hpX := epD_cut_parity α β L h X hXL
          have hpY := epD_cut_parity α β L h (L \ X) hYL
          rw [h3] at hpX
          rw [h3Y] at hpY
          exact ep33_four α β L X (L \ X) x₀ x₁ y₀ y₁ h hb hXL hY hx₀ hx₁ hx.symm hy₀ hy₁
            hy.symm h3 (by omega) (by omega)

open Classical in
/-- In a cubic bridgeless connected multigraph with at least six vertices, every vertex has an
edge that lies in two distinct perfect matchings. -/
theorem epD_vertex_two_pm {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (h : EpCubicD α β L) (hb : EpBridgeless α β L) (hconn : EpConnected α β L)
    (h6 : 6 ≤ L.card) (v : W) (hv : v ∈ L) :
    ∃ g M₁ M₂, epCross α β {v} g ∧ M₁ ∈ epPM α β L ∧ M₂ ∈ epPM α β L ∧ M₁ ≠ M₂ ∧
      g ∈ M₁ ∧ g ∈ M₂ := by
  have h4 := epD_four L.card α β L rfl h hb hconn h6
  by_contra hcon
  push Not at hcon
  -- otherwise the perfect matchings inject into the three edges at `v`
  obtain ⟨e₀, -⟩ : (epCut α β {v}).Nonempty := Finset.card_pos.mp (by rw [h.2 v hv]; omega)
  have hedge : ∀ M, M ∈ epPM α β L → ∃ g, g ∈ M ∧ epCross α β {v} g := fun M hM =>
    (hM.2 v hv).exists
  have hmaps : ∀ M ∈ (↑(epPMs α β L) : Set (Finset E)),
      (if hM : M ∈ epPM α β L then Classical.choose (hedge M hM) else e₀) ∈
        (epCut α β {v} : Finset E) := by
    intro M hM
    have hM' := (mem_epPMs _ _ _ _).mp (Finset.mem_coe.mp hM)
    rw [dif_pos hM', mem_epCut]
    exact (Classical.choose_spec (hedge M hM')).2
  have hinj : Set.InjOn (fun M => if hM : M ∈ epPM α β L then Classical.choose (hedge M hM)
      else e₀) ↑(epPMs α β L) := by
    intro M hM M' hM' heq
    have a := (mem_epPMs _ _ _ _).mp (Finset.mem_coe.mp hM)
    have b := (mem_epPMs _ _ _ _).mp (Finset.mem_coe.mp hM')
    simp only [dif_pos a, dif_pos b] at heq
    by_contra hne
    have s1 := Classical.choose_spec (hedge M a)
    have s2 := Classical.choose_spec (hedge M' b)
    exact hcon _ M M' s1.2 a b hne s1.1 (heq ▸ s2.1)
  have hle := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [h.2 v hv] at hle
  unfold epM at h4
  omega

set_option maxHeartbeats 1600000 in
open Classical in
/-- **Lemma 6, 3-twigs, core case.** In a cubic bridgeless connected multigraph with at least
six vertices, the complement of a vertex is a burl. -/
theorem ep_twig3_core {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (h : EpCubicD α β L) (hb : EpBridgeless α β L) (hconn : EpConnected α β L)
    (h6 : 6 ≤ L.card) (t : W) (ht : t ∈ L) : EpBurl α β (L.erase t) := by
  obtain ⟨g, M₁, M₂, hgt, hM₁, hM₂, hM12, hg1, hg2⟩ :=
    epD_vertex_two_pm α β L h hb hconn h6 t ht
  have hXL : L.erase t ⊆ L := Finset.erase_subset _ _
  have hlive := epD_live_of_cross h {t} g hgt
  -- crossing `L.erase t` is the same as crossing `{t}`
  have hcr : ∀ f, epCross α β (L.erase t) f ↔ epCross α β {t} f := by
    intro f
    by_cases hf : α f = β f
    · have h1 : ¬epCross α β (L.erase t) f := by unfold epCross; rw [hf]; tauto
      have h2 : ¬epCross α β {t} f := by unfold epCross; rw [hf]; tauto
      exact iff_of_false h1 h2
    · have hl : α f ∈ L ∧ β f ∈ L := by
        rcases h.1 f with h' | h'
        · exact ⟨h'.1, h'.2.1⟩
        · exact absurd h'.2.symm hf
      unfold epCross
      simp only [Finset.mem_erase, Finset.mem_singleton, hl.1, hl.2, and_true]
      tauto
  have hcut3 : (epCut α β (L.erase t)).card = 3 := by
    have : epCut α β (L.erase t) = epCut α β {t} := by
      ext f; rw [mem_epCut, mem_epCut, hcr]
    rw [this]; exact h.2 t ht
  have hnl : ∀ f, α f ∈ L.erase t → α f ≠ β f := by
    intro f hf
    rcases h.1 f with h' | h'
    · exact h'.2.2
    · exact absurd (hXL hf) h'.1
  -- a perfect matching through `g` is a local matching all of whose other edges avoid `t`
  have hPM : ∀ M, M ∈ epPM α β L → g ∈ M →
      M ∈ epLM α β (L.erase t) ∧ ∀ f ∈ M, f ≠ g → α f ∈ L.erase t ∧ β f ∈ L.erase t := by
    intro M hM hgM
    have hends : ∀ f ∈ M, f ≠ g → α f ∈ L.erase t ∧ β f ∈ L.erase t := by
      intro f hf hfg
      have hl := epD_live_of_mem_pm h hM f hf
      have hfnl := hM.1 f hf
      have hnt : ¬epCross α β {t} f := fun h' => hfg ((hM.2 t ht).unique ⟨hf, h'⟩ ⟨hgM, hgt⟩)
      rw [ep_cross_ends α β f hfnl t] at hnt
      push Not at hnt
      exact ⟨Finset.mem_erase.mpr ⟨fun h' => hnt.1 h'.symm, hl.1⟩,
        Finset.mem_erase.mpr ⟨fun h' => hnt.2 h'.symm, hl.2⟩⟩
    refine ⟨⟨fun f hf => ?_, fun c hc => hM.2 c (hXL hc)⟩, hends⟩
    by_cases hfg : f = g
    · have := (hcr g).mpr hgt
      rw [hfg]; unfold epCross at this; tauto
    · exact Or.inl (hends f hf hfg).1
  intro p hp
  have hp' := hp
  obtain ⟨hp0, hpS, hp1, hpb⟩ := hp
  have hA : ∀ N, p N ≠ 0 → g ∈ N → 1 ≤ epAltNum α β (L.erase t) N := by
    intro N hN hgN
    have hNLM := hpS N hN
    have hone := epD_claim3 α β L h (L.erase t) (L.erase t) hXL (Finset.Subset.refl _) hcut3 p
      hp' N hN
    -- `N` is a perfect matching of the whole multigraph
    have hNpm : N ∈ epPM α β L := by
      refine ⟨fun f hf => ?_, fun c hc => ?_⟩
      · rcases h.1 f with h' | h'
        · exact h'.2.2
        · exact absurd (epD_live_of_mem_lm h _ hXL hNLM f hf).1 h'.1
      · by_cases hct : c = t
        · rw [hct]
          simpa only [hcr] using hone
        · exact hNLM.2 c (Finset.mem_erase.mpr ⟨hct, hc⟩)
    obtain ⟨N₂, hN₂, hgN₂, hne⟩ : ∃ N₂, N₂ ∈ epPM α β L ∧ g ∈ N₂ ∧ N ≠ N₂ := by
      by_cases hNM : N = M₁
      · exact ⟨M₂, hM₂, hg2, fun h' => hM12 (hNM.symm.trans h')⟩
      · exact ⟨M₁, hM₁, hg1, hNM⟩
    refine ep_two_LM_altNum' α β (L.erase t) hnl (hPM N₂ hN₂ hgN₂).1 hne ?_
    intro f hf
    rcases Finset.mem_symmDiff.mp hf with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact (hPM N hNpm hgN).2 f h1 (fun h' => h2 (h' ▸ hgN₂))
    · exact (hPM N₂ hN₂ hgN₂).2 f h1 (fun h' => h2 (h' ▸ hgN))
  have hgX : α g ∈ L.erase t ∨ β g ∈ L.erase t := by
    have := (hcr g).mpr hgt
    unfold epCross at this; tauto
  rw [← hpb g hgX]
  refine Finset.sum_le_sum fun N _ => ?_
  by_cases hN : p N = 0
  · rw [hN, zero_mul, zero_mul]
  · refine mul_le_mul_of_nonneg_left ?_ (hp0 N)
    unfold epInd
    by_cases hg : g ∈ N
    · rw [if_pos hg]; exact_mod_cast hA N hN hg
    · rw [if_neg hg]; exact Nat.cast_nonneg _

open Classical in
/-- **Lemma 6, 3-twigs.** In a cubic bridgeless connected multigraph, a vertex set with a cut of
size three and at least five vertices is a burl. -/
theorem ep_twig3_burl {W E : Type*} [Fintype E] (α β : E → W) (L X : Finset W)
    (h : EpCubicD α β L) (hb : EpBridgeless α β L) (hconn : EpConnected α β L) (hXL : X ⊆ L)
    (h3 : (epCut α β X).card = 3) (h5 : 5 ≤ X.card) : EpBurl α β X := by
  have hY : ∀ w, w ∈ L \ X ↔ w ∈ L ∧ w ∉ X := fun w => Finset.mem_sdiff
  have hYL : L \ X ⊆ L := Finset.sdiff_subset
  have hsd : (L \ X).card = L.card - X.card := Finset.card_sdiff_of_subset hXL
  have hle := Finset.card_le_card hXL
  have h3Y : (epCut α β (L \ X)).card = 3 := by
    have : epCut α β (L \ X) = epCut α β X := by
      ext g; rw [mem_epCut, mem_epCut]; exact epD_cross_compl α β L X (L \ X) h hY g
    rw [this]; exact h3
  have hpY := epD_cut_parity α β L h (L \ X) hYL
  rw [h3Y] at hpY
  by_cases h1 : (L \ X).card = 1
  · -- `X` is the complement of a vertex
    obtain ⟨t, ht⟩ := Finset.card_eq_one.mp h1
    have htL : t ∈ L := hYL (by rw [ht]; exact Finset.mem_singleton_self t)
    have hXeq : X = L.erase t := by
      ext w
      rw [Finset.mem_erase]
      constructor
      · intro hw
        refine ⟨fun h' => ?_, hXL hw⟩
        have : t ∈ L \ X := by rw [ht]; exact Finset.mem_singleton_self t
        exact (Finset.mem_sdiff.mp this).2 (h' ▸ hw)
      · rintro ⟨hwt, hw⟩
        by_contra h'
        have : w ∈ L \ X := Finset.mem_sdiff.mpr ⟨hw, h'⟩
        rw [ht, Finset.mem_singleton] at this
        exact hwt this
    rw [hXeq]
    exact ep_twig3_core α β L h hb hconn (by omega) t htL
  · obtain ⟨y₀, hy₀, y₁, hy₁, hy⟩ := Finset.one_lt_card.mp (by omega : 1 < (L \ X).card)
    obtain ⟨hc₁, hb₁⟩ := epCon_cubic α β L (L \ X) y₀ y₁ h hb hYL hy₀ hy₁ hy.symm h3Y
    have hconn₁ := epCon_connected α β L (L \ X) y₀ y₁ hYL hy₀ hconn
    have hcard := epL'_card L (L \ X) y₀ hYL hy₀
    have hy₀L' : y₀ ∈ epL' L (L \ X) y₀ := by unfold epL'; exact Finset.mem_insert_self _ _
    have hXeq : X = (epL' L (L \ X) y₀).erase y₀ := by
      ext w
      unfold epL'
      rw [Finset.mem_erase, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_sdiff]
      constructor
      · intro hw
        refine ⟨fun h' => ?_, Or.inr ⟨hXL hw, fun h' => h'.2 hw⟩⟩
        exact (Finset.mem_sdiff.mp hy₀).2 (h' ▸ hw)
      · rintro ⟨hwy, h' | ⟨h1', h2'⟩⟩
        · exact absurd h' hwy
        · by_contra hwX; exact h2' ⟨h1', hwX⟩
    have hcore := ep_twig3_core _ _ _ hc₁ hb₁ hconn₁ (by omega) y₀ hy₀L'
    rw [← hXeq] at hcore
    exact (epCon_burl α β L (L \ X) X y₀ y₁ h hYL hy₀ hy₁ hXL
      (fun w hw h' => (Finset.mem_sdiff.mp h').2 hw) hcore).1

set_option maxHeartbeats 1600000 in
open Classical in
/-- **Lemma 17.** A vertex set with a cut of size four whose induced subgraph has two distinct
perfect matchings is a burl. -/
theorem ep_cut4_burl {W E : Type*} [Fintype E] (α β : E → W) (L X : Finset W)
    (h : EpCubicD α β L) (hXL : X ⊆ L) (h4 : (epCut α β X).card = 4)
    (N₁ N₂ : Finset E) (hN₁ : N₁ ∈ epLM α β X) (hN₂ : N₂ ∈ epLM α β X) (hne : N₁ ≠ N₂)
    (hc₁ : ∀ g ∈ N₁, ¬epCross α β X g) (hc₂ : ∀ g ∈ N₂, ¬epCross α β X g) :
    EpBurl α β X := by
  have hnl : ∀ g, α g ∈ X → α g ≠ β g := by
    intro g hg
    rcases h.1 g with h' | h'
    · exact h'.2.2
    · exact absurd (hXL hg) h'.1
  have hXeven : X.card % 2 = 0 := by
    rw [← epD_cut_parity α β L h X hXL, h4]
  -- edges of a local matching with no cut edge lie inside `X`
  have hinside : ∀ N, N ∈ epLM α β X → (∀ g ∈ N, ¬epCross α β X g) →
      ∀ g ∈ N, α g ∈ X ∧ β g ∈ X := by
    intro N hN hc g hg
    have hnc := hc g hg
    unfold epCross at hnc
    rcases hN.1 g hg with h' | h'
    · exact ⟨h', by by_contra h''; exact hnc (Or.inl ⟨h', h''⟩)⟩
    · exact ⟨by by_contra h''; exact hnc (Or.inr ⟨h'', h'⟩), h'⟩
  intro p hp
  obtain ⟨hp0, hpS, hp1, hpb⟩ := hp
  -- parity of the number of cut edges of a local matching
  have hpar : ∀ N, N ∈ epLM α β X → (N.filter (epCross α β X)).card % 2 = 0 := by
    intro N hN
    have hNnl : ∀ g ∈ N, α g ≠ β g := by
      intro g hg
      rcases h.1 g with h' | h'
      · exact h'.2.2
      · exact absurd (epD_live_of_mem_lm h X hXL hN g hg).1 h'.1
    have hd := ep_double_count α β N hNnl X
    have h1 : ∀ c ∈ X, (N.filter (epCross α β {c})).card = 1 :=
      fun c hcX => (ep_unique_iff_card N _).mp (hN.2 c hcX)
    rw [Finset.sum_congr rfl h1, Finset.sum_const, smul_eq_mul, mul_one] at hd
    omega
  have hA : ∀ N, p N ≠ 0 → (N.filter (epCross α β X)).card = 0 →
      1 ≤ epAltNum α β X N := by
    intro N hN h0
    have hNLM := hpS N hN
    have hNc : ∀ g ∈ N, ¬epCross α β X g := by
      intro g hg hgc
      have : g ∈ N.filter (epCross α β X) := Finset.mem_filter.mpr ⟨hg, hgc⟩
      rw [Finset.card_eq_zero.mp h0] at this
      exact absurd this (Finset.notMem_empty g)
    obtain ⟨N', hN', hc', hne'⟩ : ∃ N', N' ∈ epLM α β X ∧ (∀ g ∈ N', ¬epCross α β X g) ∧
        N ≠ N' := by
      by_cases hNN : N = N₁
      · exact ⟨N₂, hN₂, hc₂, fun h' => hne (hNN.symm.trans h')⟩
      · exact ⟨N₁, hN₁, hc₁, hNN⟩
    refine ep_two_LM_altNum' α β X hnl hN' hne' ?_
    intro g hg
    rcases Finset.mem_symmDiff.mp hg with ⟨h', -⟩ | ⟨h', -⟩
    · exact hinside N hNLM hNc g h'
    · exact hinside N' hN' hc' g h'
  -- the expected number of cut edges is 4/3
  have hexp : ∑ N, p N * ((N.filter (epCross α β X)).card : ℝ) = 4 / 3 := by
    have : ∀ N, p N * ((N.filter (epCross α β X)).card : ℝ) =
        ∑ e ∈ epCut α β X, p N * epInd N e := by
      intro N; rw [← Finset.mul_sum, ep_sum_ind_cut]
    rw [Finset.sum_congr rfl (fun N _ => this N), Finset.sum_comm]
    have h3 : ∀ e ∈ epCut α β X, ∑ N, p N * epInd N e = 1 / 3 := by
      intro e he
      refine hpb e ?_
      rw [mem_epCut] at he
      rcases he with ⟨h', -⟩ | ⟨-, h'⟩
      · exact Or.inl h'
      · exact Or.inr h'
    rw [Finset.sum_congr rfl h3, Finset.sum_const, h4]; norm_num
  have hsum : ∑ N, p N * (1 - ((N.filter (epCross α β X)).card : ℝ) / 2) = 1 / 3 := by
    have : ∀ N, p N * (1 - ((N.filter (epCross α β X)).card : ℝ) / 2) =
        p N - (p N * ((N.filter (epCross α β X)).card : ℝ)) / 2 := fun N => by ring
    rw [Finset.sum_congr rfl (fun N _ => this N), Finset.sum_sub_distrib, ← Finset.sum_div,
      hexp, hp1]
    norm_num
  rw [← hsum]
  refine Finset.sum_le_sum fun N _ => ?_
  by_cases hN : p N = 0
  · rw [hN, zero_mul, zero_mul]
  · refine mul_le_mul_of_nonneg_left ?_ (hp0 N)
    have hpN := hpar N (hpS N hN)
    by_cases h0 : (N.filter (epCross α β X)).card = 0
    · rw [h0]
      have := hA N hN h0
      have h1 : (1 : ℝ) ≤ (epAltNum α β X N : ℝ) := by exact_mod_cast this
      simpa using h1
    · have h2 : 2 ≤ (N.filter (epCross α β X)).card := by omega
      have h2' : (2 : ℝ) ≤ ((N.filter (epCross α β X)).card : ℝ) := by exact_mod_cast h2
      have h3 : (0 : ℝ) ≤ (epAltNum α β X N : ℝ) := Nat.cast_nonneg _
      linarith

/-- A laminar family: any two members are nested or disjoint. -/
def EpLaminar {W : Type*} [DecidableEq W] (𝒮 : Finset (Finset W)) : Prop :=
  ∀ S ∈ 𝒮, ∀ S' ∈ 𝒮, S ⊆ S' ∨ S' ⊆ S ∨ Disjoint S S'

/-- The atom of a node `N` of a laminar family: the part of `N` not covered by members of the
family strictly inside `N`. In the tree picture this is `φ⁻¹(N)`. -/
def epAtom {W : Type*} [DecidableEq W] (𝒮 : Finset (Finset W)) (N : Finset W) : Finset W :=
  N \ (𝒮.filter (fun C => C ⊂ N)).biUnion id

/-- The children of a node: the maximal members strictly inside it. -/
def epChildren {W : Type*} [DecidableEq W] (𝒮 : Finset (Finset W)) (N : Finset W) :
    Finset (Finset W) :=
  𝒮.filter (fun C => C ⊂ N ∧ ∀ D ∈ 𝒮, C ⊂ D → ¬D ⊂ N)

lemma mem_epAtom {W : Type*} [DecidableEq W] (𝒮 : Finset (Finset W)) (N : Finset W) (v : W) :
    v ∈ epAtom 𝒮 N ↔ v ∈ N ∧ ∀ C ∈ 𝒮, C ⊂ N → v ∉ C := by
  unfold epAtom
  simp only [Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_filter, id]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun C hC hCN hv => h2 ⟨C, ⟨hC, hCN⟩, hv⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun ⟨C, ⟨hC, hCN⟩, hv⟩ => h2 C hC hCN hv⟩

/-- **Dictionary, part 1.** The atoms of the nodes (the members of the family and the root `L`)
partition `L`: every vertex lies in the atom of exactly one node. -/
theorem ep_atom_partition {W : Type*} [DecidableEq W] (𝒮 : Finset (Finset W)) (L : Finset W)
    (hlam : EpLaminar 𝒮) (hsub : ∀ S ∈ 𝒮, S ⊆ L) (v : W) (hv : v ∈ L) :
    ∃! N, N ∈ insert L 𝒮 ∧ v ∈ epAtom 𝒮 N := by
  -- a smallest node containing `v`
  have hne : ((insert L 𝒮).filter (fun N => v ∈ N)).Nonempty :=
    ⟨L, Finset.mem_filter.mpr ⟨Finset.mem_insert_self _ _, hv⟩⟩
  obtain ⟨N, hN, hmin⟩ := Finset.exists_min_image _ Finset.card hne
  rw [Finset.mem_filter] at hN
  have hcomp : ∀ A ∈ insert L 𝒮, ∀ B ∈ insert L 𝒮, v ∈ A → v ∈ B → A ⊆ B ∨ B ⊆ A := by
    intro A hA B hB hvA hvB
    rcases Finset.mem_insert.mp hA with rfl | hA'
    · right
      rcases Finset.mem_insert.mp hB with rfl | hB'
      · exact Finset.Subset.refl _
      · exact hsub B hB'
    · rcases Finset.mem_insert.mp hB with rfl | hB'
      · exact Or.inl (hsub A hA')
      · rcases hlam A hA' B hB' with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd hvB (Finset.disjoint_left.mp h hvA)
  refine ⟨N, ⟨hN.1, (mem_epAtom 𝒮 N v).mpr ⟨hN.2, fun C hC hCN hvC => ?_⟩⟩, ?_⟩
  · have := hmin C (Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem hC, hvC⟩)
    exact absurd (Finset.card_lt_card hCN) (not_lt.mpr this)
  · rintro N' ⟨hN', hvN'⟩
    rw [mem_epAtom] at hvN'
    have hN'ne : ∀ A, A ∈ insert L 𝒮 → A ⊂ N' → A ∈ 𝒮 := by
      intro A hA hAN'
      rcases Finset.mem_insert.mp hA with rfl | hA'
      · exfalso
        have hN'L : N' ⊆ A := by
          rcases Finset.mem_insert.mp hN' with rfl | h'
          · exact Finset.Subset.refl _
          · exact hsub N' h'
        exact hAN'.2 hN'L
      · exact hA'
    rcases hcomp N hN.1 N' hN' hN.2 hvN'.1 with h | h
    · by_contra hne'
      have hss : N ⊂ N' := Finset.ssubset_iff_subset_ne.mpr ⟨h, fun h' => hne' h'.symm⟩
      exact hvN'.2 N (hN'ne N hN.1 hss) hss hN.2
    · by_contra hne'
      have hss : N' ⊂ N := Finset.ssubset_iff_subset_ne.mpr ⟨h, hne'⟩
      have := hmin N' (Finset.mem_filter.mpr ⟨hN', hvN'.1⟩)
      exact absurd (Finset.card_lt_card hss) (not_lt.mpr this)

/-- **Dictionary, part 2.** A member `S` of the family is the union of the atoms of the nodes
inside it (the preimage of the subtree below the tree edge `S`). -/
theorem ep_subtree_atoms {W : Type*} [DecidableEq W] (𝒮 : Finset (Finset W)) (L : Finset W)
    (hlam : EpLaminar 𝒮) (hsub : ∀ S ∈ 𝒮, S ⊆ L) (S : Finset W) (hS : S ∈ 𝒮) :
    S = (𝒮.filter (fun N => N ⊆ S)).biUnion (epAtom 𝒮) := by
  ext v
  rw [Finset.mem_biUnion]
  constructor
  · intro hv
    obtain ⟨N, ⟨hN, hvN⟩, -⟩ := ep_atom_partition 𝒮 L hlam hsub v (hsub S hS hv)
    have hvN' := (mem_epAtom 𝒮 N v).mp hvN
    -- `N ⊆ S`, otherwise `S ⊂ N` and `v` is not in the atom of `N`
    have hNS : N ⊆ S := by
      by_contra hns
      have hSN : S ⊆ N := by
        rcases Finset.mem_insert.mp hN with rfl | hN'
        · exact hsub S hS
        · rcases hlam S hS N hN' with h | h | h
          · exact h
          · exact absurd h hns
          · exact absurd hvN'.1 (Finset.disjoint_left.mp h hv)
      have hss : S ⊂ N := Finset.ssubset_iff_subset_ne.mpr ⟨hSN, fun h' => hns (h' ▸ Finset.Subset.refl _)⟩
      exact hvN'.2 S hS hss hv
    have hN𝒮 : N ∈ 𝒮 := by
      rcases Finset.mem_insert.mp hN with rfl | hN'
      · have : S = N := Finset.Subset.antisymm (hsub S hS) hNS
        exact this ▸ hS
      · exact hN'
    exact ⟨N, Finset.mem_filter.mpr ⟨hN𝒮, hNS⟩, hvN⟩
  · rintro ⟨N, hN, hvN⟩
    exact (Finset.mem_filter.mp hN).2 ((mem_epAtom 𝒮 N v).mp hvN).1

/-- **Dictionary, part 3.** The atom of a node is the node minus the union of its children. -/
theorem ep_atom_children {W : Type*} [DecidableEq W] (𝒮 : Finset (Finset W)) (N : Finset W) :
    epAtom 𝒮 N = N \ (epChildren 𝒮 N).biUnion id := by
  ext v
  rw [mem_epAtom, Finset.mem_sdiff, Finset.mem_biUnion]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rintro ⟨C, hC, hvC⟩
    unfold epChildren at hC
    rw [Finset.mem_filter] at hC
    exact h2 C hC.1 hC.2.1 hvC
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun C hC hCN hvC => h2 ?_⟩
    -- a largest member strictly inside `N` containing `C`
    have hne : (𝒮.filter (fun D => C ⊆ D ∧ D ⊂ N)).Nonempty :=
      ⟨C, Finset.mem_filter.mpr ⟨hC, Finset.Subset.refl _, hCN⟩⟩
    obtain ⟨D, hD, hmax⟩ := Finset.exists_max_image _ Finset.card hne
    rw [Finset.mem_filter] at hD
    refine ⟨D, ?_, hD.2.1 hvC⟩
    unfold epChildren
    rw [Finset.mem_filter]
    refine ⟨hD.1, hD.2.2, fun D' hD' hDD' hD'N => ?_⟩
    have := hmax D' (Finset.mem_filter.mpr ⟨hD', hD.2.1.trans hDD'.1, hD'N⟩)
    exact absurd (Finset.card_lt_card hDD') (not_lt.mpr this)

open Classical in
lemma ep2_connected {W E : Type*} [Fintype E] (α β : E → W) (L X : Finset W) (e e' : E)
    (x₁ : W) (hXL : X ⊆ L) (hx₁ : x₁ ∈ X) (hcut : ∀ g, epCross α β X g ↔ g = e ∨ g = e')
    (hconn : EpConnected α β L) :
    EpConnected (ep2A α β X e e' x₁) (ep2B α β X e e' x₁) (L \ X) := by
  intro T' hT' hne hneL
  have hTX : ∀ w, w ∈ T' → w ∉ X := fun w hw => (Finset.mem_sdiff.mp (hT' hw)).2
  have hTL : T' ⊆ L := fun w hw => (Finset.mem_sdiff.mp (hT' hw)).1
  rw [ep2_cut α β X e e' x₁ hcut T' hTX]
  unfold ep2Lift
  by_cases ha : epOut α β X e' ∈ T'
  · rw [if_pos ha]
    refine hconn _ (Finset.union_subset hTL hXL) ?_ ?_
    · obtain ⟨w, hw⟩ := hne; exact ⟨w, Finset.mem_union_left _ hw⟩
    · intro hL
      apply hneL
      refine Finset.Subset.antisymm hT' ?_
      intro w hw
      rw [Finset.mem_sdiff] at hw
      have : w ∈ T' ∪ X := hL ▸ hw.1
      exact (Finset.mem_union.mp this).resolve_right hw.2
  · rw [if_neg ha]
    refine hconn _ hTL hne ?_
    intro hL
    exact hTX x₁ (hL ▸ hXL hx₁) hx₁

open Classical in
/-- **Lemma 7(2) for 2-cuts with `k₁ = 1`.** If every live edge of the contraction that removes
`X` lies in at least `k` perfect matchings, so does every live edge of `G`. -/
theorem ep2_mstar_le {W E : Type*} [Fintype E] (α β : E → W) (L X Y : Finset W) (e e' : E)
    (x₁ y₁ : W) (h : EpCubicD α β L) (hb : EpBridgeless α β L) (hXL : X ⊆ L)
    (hY : ∀ w, w ∈ Y ↔ w ∈ L ∧ w ∉ X) (hx₁ : x₁ ∈ X) (hy₁ : y₁ ∈ Y) (hee' : e ≠ e')
    (hcut : ∀ g, epCross α β X g ↔ g = e ∨ g = e') (k : ℕ)
    (h₂ : ∀ g, ep2A α β X e e' x₁ g ∈ L \ X →
      k ≤ epMe (ep2A α β X e e' x₁) (ep2B α β X e e' x₁) (L \ X) g)
    (g : E) (hg : α g ∈ L) : k ≤ epMe α β L g := by
  have hYL : Y ⊆ L := fun w hw => ((hY w).mp hw).1
  have hcutY := ep2_cut_compl α β L X Y e e' h hY hcut
  obtain ⟨hc₁, hb₁⟩ := ep2_cubic α β L Y e e' y₁ h hb hYL hy₁ hee' hcutY
  have h₁ : ∀ g', ep2A α β Y e e' y₁ g' ∈ L \ Y →
      1 ≤ epMe (ep2A α β Y e e' y₁) (ep2B α β Y e e' y₁) (L \ Y) g' := by
    intro g' hg'
    obtain ⟨M, hM, hgM⟩ := epD_edge_in_pm _ _ _ hc₁ hb₁ g' hg'
    unfold epMe
    exact Finset.card_pos.mpr ⟨M, Finset.mem_filter.mpr ⟨(mem_epPMs _ _ _ _).mpr hM, hgM⟩⟩
  have := ep2_mstar α β L X Y e e' x₁ y₁ h hb hXL hY hx₁ hy₁ hee' hcut 1 k h₁ h₂ g hg
  rwa [one_mul] at this

open Classical in
/-- A small-cut-decomposition rooted at the vertex `r`, as a laminar family of vertex sets not
containing `r`, each with a cut of size two or three, satisfying the node condition
`|φ⁻¹(t)| + deg(t) ≥ 3` at every node (the members of the family and the root `L`). -/
def EpDecomp {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (r : W)
    (𝒮 : Finset (Finset W)) : Prop :=
  EpLaminar 𝒮 ∧
    (∀ S ∈ 𝒮, S ⊆ L ∧ S.Nonempty ∧ r ∉ S ∧
      ((epCut α β S).card = 2 ∨ (epCut α β S).card = 3)) ∧
    ∀ N ∈ insert L 𝒮, 3 ≤ (epAtom 𝒮 N).card + (epChildren 𝒮 N).card + (if N = L then 0 else 1)

open Classical in
/-- The decomposition refines the collection `𝒴`: every member of `𝒴` is the atom of a leaf. -/
def EpRefines {W : Type*} (L : Finset W) (r : W) (𝒮 𝒴 : Finset (Finset W)) : Prop :=
  ∀ Y ∈ 𝒴, (Y ∈ 𝒮 ∧ epChildren 𝒮 Y = ∅) ∨
    (r ∈ Y ∧ Y = epAtom 𝒮 L ∧ (epChildren 𝒮 L).card = 1)

open Classical in
/-- The root of a decomposition lies in the atom of the root node. -/
lemma EpDecomp.root_mem {W E : Type*} [Fintype E] {α β : E → W} {L : Finset W} {r : W}
    {𝒮 : Finset (Finset W)} (h : EpDecomp α β L r 𝒮) (hr : r ∈ L) : r ∈ epAtom 𝒮 L := by
  rw [mem_epAtom]
  exact ⟨hr, fun C hC _ => (h.2.1 C hC).2.2.1⟩

open Classical in
/-- **Existence of a `𝒴`-maximum decomposition**: among the decompositions refining `𝒴` (if
there is one) there is one with the largest number of members. -/
theorem ep_exists_max_decomp {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (r : W)
    (𝒴 : Finset (Finset W)) (𝒮₀ : Finset (Finset W)) (h₀ : EpDecomp α β L r 𝒮₀)
    (hr₀ : EpRefines L r 𝒮₀ 𝒴) :
    ∃ 𝒮, EpDecomp α β L r 𝒮 ∧ EpRefines L r 𝒮 𝒴 ∧
      ∀ 𝒮', EpDecomp α β L r 𝒮' → EpRefines L r 𝒮' 𝒴 → 𝒮'.card ≤ 𝒮.card := by
  have hmem : ∀ 𝒮, EpDecomp α β L r 𝒮 → 𝒮 ∈ L.powerset.powerset := by
    intro 𝒮 h𝒮
    rw [Finset.mem_powerset]
    intro S hS
    rw [Finset.mem_powerset]
    exact (h𝒮.2.1 S hS).1
  have hne : (L.powerset.powerset.filter
      (fun 𝒮 => EpDecomp α β L r 𝒮 ∧ EpRefines L r 𝒮 𝒴)).Nonempty :=
    ⟨𝒮₀, Finset.mem_filter.mpr ⟨hmem 𝒮₀ h₀, h₀, hr₀⟩⟩
  obtain ⟨𝒮, h𝒮, hmax⟩ := Finset.exists_max_image _ Finset.card hne
  rw [Finset.mem_filter] at h𝒮
  exact ⟨𝒮, h𝒮.2.1, h𝒮.2.2, fun 𝒮' h1 h2 =>
    hmax 𝒮' (Finset.mem_filter.mpr ⟨hmem 𝒮' h1, h1, h2⟩)⟩

open Classical in
/-- One cut-contraction step: contraction of a side `X` of a 3-edge-cut to a vertex, or of a
side of a 2-edge-cut by redirection. -/
def EpStep {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (α' β' : E → W)
    (L' : Finset W) : Prop :=
  (∃ X x₀ x₁, X ⊆ L ∧ x₀ ∈ X ∧ x₁ ∈ X ∧ x₁ ≠ x₀ ∧ (epCut α β X).card = 3 ∧
    α' = epConA α β X x₀ x₁ ∧ β' = epConB α β X x₀ x₁ ∧ L' = epL' L X x₀) ∨
  (∃ X e e' x₁, X ⊆ L ∧ x₁ ∈ X ∧ e ≠ e' ∧ (∀ g, epCross α β X g ↔ g = e ∨ g = e') ∧
    α' = ep2A α β X e e' x₁ ∧ β' = ep2B α β X e e' x₁ ∧ L' = L \ X)

open Classical in
/-- A cut-contraction step preserves "cubic (with dead edges), bridgeless, connected" and does
not increase the number of vertices. -/
theorem EpStep.preserves {W E : Type*} [Fintype E] {α β : E → W} {L : Finset W}
    {α' β' : E → W} {L' : Finset W} (hs : EpStep α β L α' β' L') (h : EpCubicD α β L)
    (hb : EpBridgeless α β L) (hconn : EpConnected α β L) :
    EpCubicD α' β' L' ∧ EpBridgeless α' β' L' ∧ EpConnected α' β' L' ∧ L' ⊆ L ∧
      L'.card < L.card := by
  rcases hs with ⟨X, x₀, x₁, hXL, hx₀, hx₁, hne, h3, rfl, rfl, rfl⟩ |
    ⟨X, e, e', x₁, hXL, hx₁, hee', hcut, rfl, rfl, rfl⟩
  · obtain ⟨hc, hb'⟩ := epCon_cubic α β L X x₀ x₁ h hb hXL hx₀ hx₁ hne h3
    refine ⟨hc, hb', epCon_connected α β L X x₀ x₁ hXL hx₀ hconn, ?_, ?_⟩
    · intro w hw
      unfold epL' at hw
      rw [Finset.mem_insert, Finset.mem_sdiff] at hw
      rcases hw with rfl | ⟨hw, -⟩
      · exact hXL hx₀
      · exact hw
    · rw [epL'_card L X x₀ hXL hx₀]
      have h2 : 2 ≤ X.card := Finset.one_lt_card.mpr ⟨x₁, hx₁, x₀, hx₀, hne⟩
      have := Finset.card_le_card hXL
      omega
  · obtain ⟨hc, hb'⟩ := ep2_cubic α β L X e e' x₁ h hb hXL hx₁ hee' hcut
    refine ⟨hc, hb', ep2_connected α β L X e e' x₁ hXL hx₁ hcut hconn, Finset.sdiff_subset, ?_⟩
    rw [Finset.card_sdiff_of_subset hXL]
    have h1 : 1 ≤ X.card := Finset.card_pos.mpr ⟨x₁, hx₁⟩
    have := Finset.card_le_card hXL
    omega

/-- The multigraph `(α', β', L')` is obtained from `(α, β, L)` by a sequence of
cut-contractions. -/
def EpReach {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (α' β' : E → W)
    (L' : Finset W) : Prop :=
  Relation.ReflTransGen
    (fun a b : (E → W) × (E → W) × Finset W => EpStep a.1 a.2.1 a.2.2 b.1 b.2.1 b.2.2)
    (α, β, L) (α', β', L')

/-- `G` has a core: some sequence of cut-contractions leads to a cyclically 4-edge-connected
multigraph with at least six vertices. -/
def EpHasCore {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) : Prop :=
  ∃ α' β' L', EpReach α β L α' β' L' ∧ EpCyc4 α' β' L' ∧ 6 ≤ L'.card

theorem EpReach.preserves {W E : Type*} [Fintype E] {α β : E → W} {L : Finset W}
    {α' β' : E → W} {L' : Finset W} (hr : EpReach α β L α' β' L') (h : EpCubicD α β L)
    (hb : EpBridgeless α β L) (hconn : EpConnected α β L) :
    EpCubicD α' β' L' ∧ EpBridgeless α' β' L' ∧ EpConnected α' β' L' ∧ L' ⊆ L := by
  unfold EpReach at hr
  have key : ∀ b : (E → W) × (E → W) × Finset W,
      Relation.ReflTransGen
        (fun a b : (E → W) × (E → W) × Finset W => EpStep a.1 a.2.1 a.2.2 b.1 b.2.1 b.2.2)
        (α, β, L) b →
      EpCubicD b.1 b.2.1 b.2.2 ∧ EpBridgeless b.1 b.2.1 b.2.2 ∧ EpConnected b.1 b.2.1 b.2.2 ∧
        b.2.2 ⊆ L := by
    intro b hb'
    induction hb' with
    | refl => exact ⟨h, hb, hconn, Finset.Subset.refl _⟩
    | tail _ hstep ih =>
      obtain ⟨a1, a2, a3, a4, -⟩ := EpStep.preserves hstep ih.1 ih.2.1 ih.2.2.1
      exact ⟨a1, a2, a3, a4.trans ih.2.2.2⟩
  exact key (α', β', L') hr

/-- If a contraction has a core, so does the original multigraph. -/
theorem EpHasCore.of_step {W E : Type*} [Fintype E] {α β : E → W} {L : Finset W}
    {α' β' : E → W} {L' : Finset W} (hs : EpStep α β L α' β' L') (hc : EpHasCore α' β' L') :
    EpHasCore α β L := by
  obtain ⟨α'', β'', L'', hr, h4, h6⟩ := hc
  exact ⟨α'', β'', L'', Relation.ReflTransGen.head hs hr, h4, h6⟩

set_option maxHeartbeats 800000 in
open Classical in
/-- **Lemma 7(2) along a cut-contraction step:** a lower bound for the number of perfect
matchings through every live edge of the contraction holds for `G` as well. -/
theorem EpStep.mstar_le {W E : Type*} [Fintype E] {α β : E → W} {L : Finset W}
    {α' β' : E → W} {L' : Finset W} (hs : EpStep α β L α' β' L') (h : EpCubicD α β L)
    (hb : EpBridgeless α β L) (k : ℕ) (hk : ∀ g, α' g ∈ L' → k ≤ epMe α' β' L' g)
    (g : E) (hg : α g ∈ L) : k ≤ epMe α β L g := by
  rcases hs with ⟨X, x₀, x₁, hXL, hx₀, hx₁, hne, h3, rfl, rfl, rfl⟩ |
    ⟨X, e, e', x₁, hXL, hx₁, hee', hcut, rfl, rfl, rfl⟩
  · have hY : ∀ w, w ∈ L \ X ↔ w ∈ L ∧ w ∉ X := fun w => Finset.mem_sdiff
    have hYL : L \ X ⊆ L := Finset.sdiff_subset
    have h3Y : (epCut α β (L \ X)).card = 3 := by
      have : epCut α β (L \ X) = epCut α β X := by
        ext g'; rw [mem_epCut, mem_epCut]; exact epD_cross_compl α β L X (L \ X) h hY g'
      rw [this]; exact h3
    have hpar := epD_cut_parity α β L h (L \ X) hYL
    rw [h3Y] at hpar
    by_cases h1 : (L \ X).card = 1
    · -- the other side is a single vertex: its contraction is `G` itself
      obtain ⟨y₀, hy₀⟩ := Finset.card_eq_one.mp h1
      have hy₀L : y₀ ∈ L := hYL (by rw [hy₀]; exact Finset.mem_singleton_self y₀)
      have hA : epConA α β (L \ X) y₀ y₀ = α := by
        funext g'
        unfold epConA epRho
        rw [hy₀]
        by_cases ha : α g' = y₀
        · simp [ha]
        · simp [ha]
      have hB : epConB α β (L \ X) y₀ y₀ = β := by
        funext g'
        unfold epConB epRho
        rw [hy₀]
        by_cases hb' : β g' = y₀
        · simp [hb']
        · simp [hb']
      have hL' : epL' L (L \ X) y₀ = L := by
        unfold epL'
        rw [hy₀]
        ext w
        simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton]
        constructor
        · rintro (rfl | ⟨hw, -⟩)
          · exact hy₀L
          · exact hw
        · intro hw
          by_cases hwy : w = y₀
          · exact Or.inl hwy
          · exact Or.inr ⟨hw, hwy⟩
      have h₁ : ∀ g', epConA α β (L \ X) y₀ y₀ g' ∈ epL' L (L \ X) y₀ →
          1 ≤ epMe (epConA α β (L \ X) y₀ y₀) (epConB α β (L \ X) y₀ y₀)
            (epL' L (L \ X) y₀) g' := by
        rw [hA, hB, hL']
        intro g' hg'
        obtain ⟨M, hM, hgM⟩ := epD_edge_in_pm α β L h hb g' hg'
        unfold epMe
        exact Finset.card_pos.mpr ⟨M, Finset.mem_filter.mpr ⟨(mem_epPMs _ _ _ _).mpr hM, hgM⟩⟩
      have := ep3_mstar α β L X (L \ X) x₀ x₁ y₀ y₀ h hXL hY hx₀
        (by rw [hy₀]; exact Finset.mem_singleton_self y₀) 1 k h₁ hk g hg
      rwa [one_mul] at this
    · obtain ⟨y₀, hy₀, y₁, hy₁, hy⟩ := Finset.one_lt_card.mp (by omega : 1 < (L \ X).card)
      exact epCon_mstar_le α β L X (L \ X) x₀ x₁ y₀ y₁ h hb hXL hY hx₀ hy₀ hy₁ hy.symm h3 k hk
        g hg
  · have hY : ∀ w, w ∈ L \ X ↔ w ∈ L ∧ w ∉ X := fun w => Finset.mem_sdiff
    obtain ⟨a1, a2, -, -⟩ := ep_cut_insert_card α β L X h hb hXL e e' hee' hcut e (Or.inl rfl)
    exact ep2_mstar_le α β L X (L \ X) e e' x₁ (epOut α β X e) h hb hXL hY hx₁
      (Finset.mem_sdiff.mpr ⟨a1, a2⟩) hee' hcut k hk g hg

/-- Lemma 7(2) along a sequence of cut-contractions. -/
theorem EpReach.mstar_le {W E : Type*} [Fintype E] {α β : E → W} {L : Finset W}
    {α' β' : E → W} {L' : Finset W} (hr : EpReach α β L α' β' L') (h : EpCubicD α β L)
    (hb : EpBridgeless α β L) (hconn : EpConnected α β L) (k : ℕ)
    (hk : ∀ g, α' g ∈ L' → k ≤ epMe α' β' L' g) (g : E) (hg : α g ∈ L) :
    k ≤ epMe α β L g := by
  unfold EpReach at hr
  have key : ∀ b : (E → W) × (E → W) × Finset W,
      Relation.ReflTransGen
        (fun a b : (E → W) × (E → W) × Finset W => EpStep a.1 a.2.1 a.2.2 b.1 b.2.1 b.2.2)
        (α, β, L) b →
      (∀ g, b.1 g ∈ b.2.2 → k ≤ epMe b.1 b.2.1 b.2.2 g) → ∀ g, α g ∈ L → k ≤ epMe α β L g := by
    intro b hb'
    induction hb' with
    | refl => exact fun h' => h'
    | tail hprev hstep ih =>
      intro hkb
      have hp := EpReach.preserves (show EpReach α β L _ _ _ from hprev) h hb hconn
      exact ih (fun g' hg' => EpStep.mstar_le hstep hp.1 hp.2.1 k hkb g' hg')
  exact key (α', β', L') hr hk g hg

/-- A triangle: three distinct vertices `x, y, z` of `L` joined by the edges `exy, eyz, ezx`. -/
def EpTriangle {W E : Type*} (α β : E → W) (L : Finset W) (x y z : W) (exy eyz ezx : E) :
    Prop :=
  x ∈ L ∧ y ∈ L ∧ z ∈ L ∧ x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
    (∀ w, epCross α β {w} exy ↔ w = x ∨ w = y) ∧
    (∀ w, epCross α β {w} eyz ↔ w = y ∨ w = z) ∧
    (∀ w, epCross α β {w} ezx ↔ w = z ∨ w = x)

set_option maxHeartbeats 1600000 in
open Classical in
/-- Every edge leaving a triangle extends to a matching of the triangle by the opposite edge. -/
lemma ep_triangle_hfc {W E : Type*} (α β : E → W) (L : Finset W) (x y z : W)
    (exy eyz ezx : E) (ht : EpTriangle α β L x y z exy eyz ezx) :
    ∃ Nf : E → Finset E, ∀ f, epCross α β ({x, y, z} : Finset W) f →
      (∀ g ∈ Nf f, α g ∈ ({x, y, z} : Finset W) ∧ β g ∈ ({x, y, z} : Finset W) ∧ α g ≠ β g) ∧
      ∀ c ∈ ({x, y, z} : Finset W), ∃! g, g ∈ insert f (Nf f) ∧ epCross α β {c} g := by
  obtain ⟨-, -, -, hxy, hyz, hxz, Hxy, Hyz, Hzx⟩ := ht
  -- the three edges are not loops and lie inside the triangle
  have hin : ∀ (g : E) (p q : W), p ≠ q → (∀ w, epCross α β {w} g ↔ w = p ∨ w = q) →
      p ∈ ({x, y, z} : Finset W) → q ∈ ({x, y, z} : Finset W) →
      α g ∈ ({x, y, z} : Finset W) ∧ β g ∈ ({x, y, z} : Finset W) ∧ α g ≠ β g := by
    intro g p q hpq H hp hq
    have hne : α g ≠ β g := by
      intro h'
      have := (H p).mpr (Or.inl rfl)
      rw [epCross_singleton, h'] at this; tauto
    have ha := (H (α g)).mp ((ep_cross_ends α β g hne _).mpr (Or.inl rfl))
    have hb := (H (β g)).mp ((ep_cross_ends α β g hne _).mpr (Or.inr rfl))
    refine ⟨?_, ?_, hne⟩
    · rcases ha with h' | h' <;> rw [h'] <;> assumption
    · rcases hb with h' | h' <;> rw [h'] <;> assumption
  have mx : x ∈ ({x, y, z} : Finset W) := by simp
  have my : y ∈ ({x, y, z} : Finset W) := by simp
  have mz : z ∈ ({x, y, z} : Finset W) := by simp
  refine ⟨fun f => if epCross α β {x} f then {eyz} else if epCross α β {y} f then {ezx}
    else {exy}, fun f hf => ?_⟩
  dsimp only
  -- the end of `f` in the triangle is its only vertex there
  obtain ⟨v, u, hvT, huT, Hf⟩ := ep_ends_of_cross α β f _ hf
  have hfc : ∀ c, c ∈ ({x, y, z} : Finset W) → (epCross α β {c} f ↔ c = v) := by
    intro c hc
    rw [Hf]
    constructor
    · rintro (h' | h')
      · exact h'
      · exact absurd (h' ▸ hc) huT
    · exact Or.inl
  have hv : v = x ∨ v = y ∨ v = z := by simpa using hvT
  have key : ∀ (opp : E) (p q : W), (∀ w, epCross α β {w} opp ↔ w = p ∨ w = q) → p ≠ v →
      q ≠ v → ({x, y, z} : Finset W) = {v, p, q} →
      ∀ c ∈ ({x, y, z} : Finset W), ∃! g, g ∈ insert f ({opp} : Finset E) ∧
        epCross α β {c} g := by
    intro opp p q H hp hq hset c hc
    have hc' : c = v ∨ c = p ∨ c = q := by rw [hset] at hc; simpa using hc
    by_cases hcv : c = v
    · refine ⟨f, ⟨Finset.mem_insert_self _ _, (hfc c hc).mpr hcv⟩, ?_⟩
      rintro g ⟨hg, hgc⟩
      rcases Finset.mem_insert.mp hg with h' | h'
      · exact h'
      · exfalso
        rw [Finset.mem_singleton.mp h', H, hcv] at hgc
        rcases hgc with h'' | h''
        · exact hp h''.symm
        · exact hq h''.symm
    · have hopp : epCross α β {c} opp := by
        rw [H]; rcases hc' with h' | h' | h'
        · exact absurd h' hcv
        · exact Or.inl h'
        · exact Or.inr h'
      refine ⟨opp, ⟨Finset.mem_insert_of_mem (Finset.mem_singleton_self _), hopp⟩, ?_⟩
      rintro g ⟨hg, hgc⟩
      rcases Finset.mem_insert.mp hg with h' | h'
      · exact absurd ((hfc c hc).mp (h' ▸ hgc)) hcv
      · exact Finset.mem_singleton.mp h'
  have hfx : epCross α β {x} f ↔ x = v := hfc x mx
  have hfy : epCross α β {y} f ↔ y = v := hfc y my
  rcases hv with rfl | rfl | rfl
  · rw [if_pos (hfx.mpr rfl)]
    exact ⟨fun g hg => by rw [Finset.mem_singleton.mp hg]; exact hin eyz y z hyz Hyz my mz,
      key eyz y z Hyz (Ne.symm hxy) (Ne.symm hxz) rfl⟩
  · rw [if_neg (fun h' => hxy (hfx.mp h')), if_pos (hfy.mpr rfl)]
    refine ⟨fun g hg => by rw [Finset.mem_singleton.mp hg]; exact hin ezx z x (Ne.symm hxz) Hzx mz mx,
      key ezx z x Hzx (Ne.symm hyz) hxy ?_⟩
    ext w; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  · rw [if_neg (fun h' => hxz (hfx.mp h')), if_neg (fun h' => hyz (hfy.mp h'))]
    refine ⟨fun g hg => by rw [Finset.mem_singleton.mp hg]; exact hin exy x y hxy Hxy mx my,
      key exy x y Hxy hxz hyz ?_⟩
    ext w; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto

open Classical in
/-- **Lemma 10 for a triangle, foliage part.** A burl of the contraction of a triangle that
contains the new vertex gives a burl of `G` after putting the triangle back. -/
theorem ep_triangle_burl_lift {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (x y z : W) (exy eyz ezx : E) (h : EpCubicD α β L)
    (ht : EpTriangle α β L x y z exy eyz ezx)
    (h3 : (epCut α β ({x, y, z} : Finset W)).card = 3) (Z' : Finset W)
    (hZ' : Z' ⊆ epL' L ({x, y, z} : Finset W) x) (hxZ : x ∈ Z')
    (hburl : EpBurl (epConA α β ({x, y, z} : Finset W) x y)
      (epConB α β ({x, y, z} : Finset W) x y) Z') :
    EpBurl α β (Z' ∪ {x, y, z}) := by
  obtain ⟨Nf, hNf⟩ := ep_triangle_hfc α β L x y z exy eyz ezx ht
  have hTL : ({x, y, z} : Finset W) ⊆ L := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact ht.1
    · exact ht.2.1
    · exact ht.2.2.1
  exact epCon_burl_lift α β L _ Z' x y h hTL (by simp) (by simp) (Ne.symm ht.2.2.2.1) h3 Nf hNf
    hZ' hxZ hburl

set_option maxHeartbeats 1600000 in
open Classical in
/-- **Static exclusion.** In a cubic bridgeless connected multigraph, let `X` have the cut
`{e, e'}` and let `C'` be disjoint from `X` with a cut of size at most three, such that some
vertex `r` lies outside `X ∪ C'`. Then the outside ends of `e` and `e'` do not both lie in `C'`
(otherwise `δ(X ∪ C') = δ(C') \ {e, e'}` would have at most one edge). -/
theorem ep_two_cut_not_both {W E : Type*} [Fintype E] (α β : E → W) (L X C' : Finset W)
    (e e' : E) (r : W) (h : EpCubicD α β L) (hb : EpBridgeless α β L)
    (hconn : EpConnected α β L) (hXL : X ⊆ L) (hCL : C' ⊆ L)
    (hdisj : ∀ w, w ∈ X → w ∉ C') (hr : r ∈ L) (hrX : r ∉ X) (hrC : r ∉ C')
    (hee' : e ≠ e') (hcut : ∀ g, epCross α β X g ↔ g = e ∨ g = e')
    (hC3 : (epCut α β C').card ≤ 3) :
    ¬(epOut α β X e ∈ C' ∧ epOut α β X e' ∈ C') := by
  rintro ⟨ha, ha'⟩
  obtain ⟨haX, x, hx, hex⟩ := epOut_ends α β X e ((hcut e).mpr (Or.inl rfl))
  obtain ⟨ha'X, x', hx', hex'⟩ := epOut_ends α β X e' ((hcut e').mpr (Or.inr rfl))
  generalize epOut α β X e = a at *
  generalize epOut α β X e' = a' at *
  have hxC : x ∉ C' := hdisj x hx
  have hx'C : x' ∉ C' := hdisj x' hx'
  -- `e` and `e'` cross `C'` but not `X ∪ C'`
  have he : e ∈ epCut α β C' := by
    rw [mem_epCut, ep_cross_pq α β e x a hex]; exact Or.inr ⟨hxC, ha⟩
  have he' : e' ∈ epCut α β C' := by
    rw [mem_epCut, ep_cross_pq α β e' x' a' hex']; exact Or.inr ⟨hx'C, ha'⟩
  have heU : ¬epCross α β (X ∪ C') e := by
    rw [ep_cross_pq α β e x a hex]
    have m1 : x ∈ X ∪ C' := Finset.mem_union_left _ hx
    have m2 : a ∈ X ∪ C' := Finset.mem_union_right _ ha
    tauto
  have he'U : ¬epCross α β (X ∪ C') e' := by
    rw [ep_cross_pq α β e' x' a' hex']
    have m1 : x' ∈ X ∪ C' := Finset.mem_union_left _ hx'
    have m2 : a' ∈ X ∪ C' := Finset.mem_union_right _ ha'
    tauto
  have hsub : epCut α β (X ∪ C') ⊆ ((epCut α β C').erase e).erase e' := by
    intro g hg
    rw [mem_epCut] at hg
    have hge : g ≠ e := fun h' => heU (h' ▸ hg)
    have hge' : g ≠ e' := fun h' => he'U (h' ▸ hg)
    have hnX : ¬epCross α β X g := fun h' => ((hcut g).mp h').elim hge hge'
    refine Finset.mem_erase.mpr ⟨hge', Finset.mem_erase.mpr ⟨hge, ?_⟩⟩
    rw [mem_epCut]
    unfold epCross at hg hnX ⊢
    simp only [Finset.mem_union] at hg
    have d1 := hdisj (α g); have d2 := hdisj (β g)
    tauto
  have hle := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hee', he'⟩),
    Finset.card_erase_of_mem he] at hle
  have hUL : X ∪ C' ⊆ L := Finset.union_subset hXL hCL
  have h1 := hb (X ∪ C') hUL
  have h0 : (epCut α β (X ∪ C')).card = 0 := by omega
  refine hconn (X ∪ C') hUL ⟨x, Finset.mem_union_left _ hx⟩ ?_ (Finset.card_eq_zero.mp h0)
  intro hL
  have : r ∈ X ∪ C' := hL ▸ hr
  rcases Finset.mem_union.mp this with h' | h'
  · exact hrX h'
  · exact hrC h'

set_option maxHeartbeats 1600000 in
open Classical in
/-- After contracting the 2-cut side `X` by redirection, a set `C'` disjoint from `X` that does
not contain both outside ends of the cut edges has a cut of the same size as in `G`. -/
theorem ep2_cut_card_other {W E : Type*} [Fintype E] (α β : E → W) (X C' : Finset W)
    (e e' : E) (x₁ : W) (hdisj : ∀ w, w ∈ C' → w ∉ X) (hee' : e ≠ e')
    (hcut : ∀ g, epCross α β X g ↔ g = e ∨ g = e')
    (hnot : ¬(epOut α β X e ∈ C' ∧ epOut α β X e' ∈ C')) :
    (epCut (ep2A α β X e e' x₁) (ep2B α β X e e' x₁) C').card = (epCut α β C').card := by
  rw [ep2_cut α β X e e' x₁ hcut C' hdisj]
  unfold ep2Lift
  by_cases ha' : epOut α β X e' ∈ C'
  · rw [if_pos ha']
    have ha : epOut α β X e ∉ C' := fun h' => hnot ⟨h', ha'⟩
    obtain ⟨haX, x, hx, hex⟩ := epOut_ends α β X e ((hcut e).mpr (Or.inl rfl))
    obtain ⟨ha'X, x', hx', hex'⟩ := epOut_ends α β X e' ((hcut e').mpr (Or.inr rfl))
    generalize epOut α β X e = a at *
    generalize epOut α β X e' = a' at *
    have hxC : x ∉ C' := fun h' => hdisj x h' hx
    have hx'C : x' ∉ C' := fun h' => hdisj x' h' hx'
    have he' : e' ∈ epCut α β C' := by
      rw [mem_epCut, ep_cross_pq α β e' x' a' hex']; exact Or.inr ⟨hx'C, ha'⟩
    have he : e ∉ epCut α β C' := by
      rw [mem_epCut, ep_cross_pq α β e x a hex]; tauto
    have hset : epCut α β (C' ∪ X) = insert e ((epCut α β C').erase e') := by
      ext g
      rw [mem_epCut, Finset.mem_insert, Finset.mem_erase, mem_epCut]
      by_cases hge : g = e
      · rw [hge, ep_cross_pq α β e x a hex]
        have m1 : x ∈ C' ∪ X := Finset.mem_union_right _ hx
        have m2 : a ∉ C' ∪ X := fun h' => (Finset.mem_union.mp h').elim ha haX
        tauto
      · by_cases hge' : g = e'
        · rw [hge', ep_cross_pq α β e' x' a' hex']
          have m1 : x' ∈ C' ∪ X := Finset.mem_union_right _ hx'
          have m2 : a' ∈ C' ∪ X := Finset.mem_union_left _ ha'
          tauto
        · have hnX : ¬epCross α β X g := fun h' => ((hcut g).mp h').elim hge hge'
          unfold epCross at hnX ⊢
          simp only [Finset.mem_union]
          have d1 := hdisj (α g); have d2 := hdisj (β g)
          tauto
    rw [hset, Finset.card_insert_of_notMem (fun h' => he (Finset.mem_of_mem_erase h')),
      Finset.card_erase_of_mem he']
    have := Finset.card_pos.mpr ⟨e', he'⟩
    omega
  · rw [if_neg ha']

open Classical in
/-- Bookkeeping for one step of the cut correspondence between a hub and the graph. -/
lemma ep_lift_book {W : Type*} (𝒞 : Finset (Finset W)) (C : Finset W)
    (R R₁ T' Lh Z Z₁ : Finset W) (v : W)
    (hdisC : ∀ C' ∈ 𝒞.erase C, ∀ w, w ∈ C' → w ∉ C) (hC : C ∈ 𝒞)
    (hRR : R ⊆ R₁) (hR₁ : R₁ ⊆ insert v R) (hRC : ∀ w, w ∈ R → w ∉ C)
    (hZ : ∀ w, w ∉ C → (w ∈ Z ↔ w ∈ Z₁)) (hCZ : C ⊆ Z ∨ Disjoint C Z)
    (hv1 : v ∈ R₁ → v ∈ Z₁ → C ⊆ Z) (hv2 : v ∈ R₁ → v ∉ Z₁ → Disjoint C Z)
    (ih1 : ∀ w ∈ R₁, w ∈ Z₁ ↔ w ∈ T')
    (ih2 : ∀ C' ∈ 𝒞.erase C, C' ⊆ Z₁ ∨ Disjoint C' Z₁)
    (ih3 : T'.card ≤ (T' ∩ R₁).card + ((𝒞.erase C).filter (fun D => D ⊆ Z₁)).card)
    (ih4 : (Lh \ T').card ≤ (R₁ \ T').card +
      ((𝒞.erase C).filter (fun D => Disjoint D Z₁)).card) :
    (∀ w ∈ R, w ∈ Z ↔ w ∈ T') ∧ (∀ C' ∈ 𝒞, C' ⊆ Z ∨ Disjoint C' Z) ∧
      T'.card ≤ (T' ∩ R).card + (𝒞.filter (fun D => D ⊆ Z)).card ∧
      (Lh \ T').card ≤ (R \ T').card + (𝒞.filter (fun D => Disjoint D Z)).card := by
  have hmono1 : ∀ C' ∈ 𝒞.erase C, C' ⊆ Z₁ → C' ⊆ Z := fun C' hC' h' w hw =>
    (hZ w (hdisC C' hC' w hw)).mpr (h' hw)
  have hmono2 : ∀ C' ∈ 𝒞.erase C, Disjoint C' Z₁ → Disjoint C' Z := by
    intro C' hC' h'
    rw [Finset.disjoint_left] at h' ⊢
    exact fun w hw hwZ => h' hw ((hZ w (hdisC C' hC' w hw)).mp hwZ)
  have hCnot : C ∉ 𝒞.erase C := Finset.notMem_erase C 𝒞
  have hcount : ∀ (p q : Finset W → Prop) [DecidablePred p] [DecidablePred q],
      (∀ C' ∈ 𝒞.erase C, q C' → p C') →
      ((𝒞.erase C).filter q).card ≤ (𝒞.filter p).card ∧
      (p C → ((𝒞.erase C).filter q).card + 1 ≤ (𝒞.filter p).card) := by
    intro p q _ _ hpq
    have hsub : (𝒞.erase C).filter q ⊆ 𝒞.filter p := by
      intro D hD
      rw [Finset.mem_filter] at hD ⊢
      exact ⟨Finset.mem_of_mem_erase hD.1, hpq D hD.1 hD.2⟩
    refine ⟨Finset.card_le_card hsub, fun hpC => ?_⟩
    have hCn : C ∉ (𝒞.erase C).filter q := fun h' => hCnot (Finset.mem_of_mem_filter _ h')
    rw [← Finset.card_insert_of_notMem hCn]
    apply Finset.card_le_card
    intro D hD
    rcases Finset.mem_insert.mp hD with rfl | hD
    · exact Finset.mem_filter.mpr ⟨hC, hpC⟩
    · exact hsub hD
  refine ⟨fun w hw => ?_, fun C' hC' => ?_, ?_, ?_⟩
  · rw [hZ w (hRC w hw)]; exact ih1 w (hRR hw)
  · by_cases hCC : C' = C
    · rw [hCC]; exact hCZ
    · have hm : C' ∈ 𝒞.erase C := Finset.mem_erase.mpr ⟨hCC, hC'⟩
      rcases ih2 C' hm with h' | h'
      · exact Or.inl (hmono1 C' hm h')
      · exact Or.inr (hmono2 C' hm h')
  · have c1 : ((𝒞.erase C).filter (fun D => D ⊆ Z₁)).card ≤ (𝒞.filter (fun D => D ⊆ Z)).card :=
      (hcount (fun D => D ⊆ Z) (fun D => D ⊆ Z₁) hmono1).1
    have c2 : C ⊆ Z → ((𝒞.erase C).filter (fun D => D ⊆ Z₁)).card + 1 ≤
        (𝒞.filter (fun D => D ⊆ Z)).card :=
      (hcount (fun D => D ⊆ Z) (fun D => D ⊆ Z₁) hmono1).2
    by_cases hv : v ∈ R₁ ∧ v ∈ T'
    · have := c2 (hv1 hv.1 ((ih1 v hv.1).mpr hv.2))
      have hle : (T' ∩ R₁).card ≤ (T' ∩ R).card + 1 := by
        refine (Finset.card_le_card (?_ : T' ∩ R₁ ⊆ insert v (T' ∩ R))).trans
          (Finset.card_insert_le _ _)
        intro w hw
        rw [Finset.mem_inter] at hw
        rcases Finset.mem_insert.mp (hR₁ hw.2) with h' | h'
        · exact Finset.mem_insert.mpr (Or.inl h')
        · exact Finset.mem_insert_of_mem (Finset.mem_inter.mpr ⟨hw.1, h'⟩)
      omega
    · have hle : (T' ∩ R₁).card ≤ (T' ∩ R).card := by
        apply Finset.card_le_card
        intro w hw
        rw [Finset.mem_inter] at hw
        rcases Finset.mem_insert.mp (hR₁ hw.2) with rfl | h'
        · exact absurd ⟨hw.2, hw.1⟩ hv
        · exact Finset.mem_inter.mpr ⟨hw.1, h'⟩
      omega
  · have c1 : ((𝒞.erase C).filter (fun D => Disjoint D Z₁)).card ≤
        (𝒞.filter (fun D => Disjoint D Z)).card :=
      (hcount (fun D => Disjoint D Z) (fun D => Disjoint D Z₁) hmono2).1
    have c2 : Disjoint C Z → ((𝒞.erase C).filter (fun D => Disjoint D Z₁)).card + 1 ≤
        (𝒞.filter (fun D => Disjoint D Z)).card :=
      (hcount (fun D => Disjoint D Z) (fun D => Disjoint D Z₁) hmono2).2
    by_cases hv : v ∈ R₁ ∧ v ∉ T'
    · have := c2 (hv2 hv.1 (fun h' => hv.2 ((ih1 v hv.1).mp h')))
      have hle : (R₁ \ T').card ≤ (R \ T').card + 1 := by
        refine (Finset.card_le_card (?_ : R₁ \ T' ⊆ insert v (R \ T'))).trans
          (Finset.card_insert_le _ _)
        intro w hw
        rw [Finset.mem_sdiff] at hw
        rcases Finset.mem_insert.mp (hR₁ hw.1) with h' | h'
        · exact Finset.mem_insert.mpr (Or.inl h')
        · exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨h', hw.2⟩)
      omega
    · have hle : (R₁ \ T').card ≤ (R \ T').card := by
        apply Finset.card_le_card
        intro w hw
        rw [Finset.mem_sdiff] at hw
        rcases Finset.mem_insert.mp (hR₁ hw.1) with rfl | h'
        · exact absurd ⟨hw.1, hw.2⟩ hv
        · exact Finset.mem_sdiff.mpr ⟨h', hw.2⟩
      omega

set_option maxHeartbeats 3200000 in
open Classical in
/-- **Existence of hubs.** Contracting a family `𝒞` of pairwise disjoint sets with cuts of size
two or three (none containing the vertex `r`) gives a multigraph reachable by cut-contractions
that keeps the vertices outside `⋃ 𝒞`, has one new vertex for each 3-cut member, keeps the
edges between kept vertices, and reflects burls that avoid the new edges. -/
theorem ep_hub_exists {W E : Type*} [Fintype E] : ∀ (n : ℕ) (α β : E → W) (L : Finset W)
    (𝒞 : Finset (Finset W)) (r : W), 𝒞.card = n → EpCubicD α β L → EpBridgeless α β L →
    EpConnected α β L → r ∈ L →
    (∀ C ∈ 𝒞, C ⊆ L ∧ C.Nonempty ∧ r ∉ C ∧
      ((epCut α β C).card = 2 ∨ (epCut α β C).card = 3)) →
    (∀ C ∈ 𝒞, ∀ C' ∈ 𝒞, C ≠ C' → Disjoint C C') →
    ∃ (α' β' : E → W) (L' : Finset W) (newE : Finset E),
      EpReach α β L α' β' L' ∧ L \ 𝒞.biUnion id ⊆ L' ∧ L' ⊆ L ∧
      L'.card = (L \ 𝒞.biUnion id).card + (𝒞.filter (fun C => (epCut α β C).card = 3)).card ∧
      (∀ g, α g ∈ L \ 𝒞.biUnion id → β g ∈ L \ 𝒞.biUnion id → α' g = α g ∧ β' g = β g) ∧
      (∀ Z, Z ⊆ L \ 𝒞.biUnion id → (∀ g ∈ newE, ¬(α' g ∈ Z ∧ β' g ∈ Z)) → EpBurl α' β' Z →
        EpBurl α β Z ∧ (epCut α β Z).card = (epCut α' β' Z).card) ∧
      (∀ T', T' ⊆ L' → ∃ Z, Z ⊆ L ∧ (∀ w ∈ L \ 𝒞.biUnion id, w ∈ Z ↔ w ∈ T') ∧
        (∀ C ∈ 𝒞, C ⊆ Z ∨ Disjoint C Z) ∧ (epCut α β Z).card = (epCut α' β' T').card ∧
        T'.card ≤ (T' ∩ (L \ 𝒞.biUnion id)).card + (𝒞.filter (fun D => D ⊆ Z)).card ∧
        (L' \ T').card ≤ ((L \ 𝒞.biUnion id) \ T').card +
          (𝒞.filter (fun D => Disjoint D Z)).card) := by
  intro n
  induction n with
  | zero =>
    intro α β L 𝒞 r hn h hb hconn hr h𝒞 hdis
    rw [Finset.card_eq_zero] at hn
    subst hn
    refine ⟨α, β, L, ∅, Relation.ReflTransGen.refl, Finset.sdiff_subset, Finset.Subset.refl _,
      ?_, fun g _ _ => ⟨rfl, rfl⟩, fun Z _ _ hZ => ⟨hZ, rfl⟩, fun T' hT' =>
        ⟨T', hT', fun w _ => Iff.rfl, fun C hC => absurd hC (Finset.notMem_empty C), rfl, ?_, ?_⟩⟩
    · simp
    · rw [Finset.biUnion_empty, Finset.sdiff_empty, Finset.inter_eq_left.mpr hT']; omega
    · rw [Finset.biUnion_empty, Finset.sdiff_empty]; omega
  | succ n ih =>
    intro α β L 𝒞 r hn h hb hconn hr h𝒞 hdis
    obtain ⟨C, hC⟩ : 𝒞.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨hCL, hCne, hrC, hCcut⟩ := h𝒞 C hC
    have hrest_card : (𝒞.erase C).card = n := by rw [Finset.card_erase_of_mem hC]; omega
    have hU : 𝒞.biUnion id = C ∪ (𝒞.erase C).biUnion id := by
      ext w
      simp only [Finset.mem_biUnion, Finset.mem_union, Finset.mem_erase, id]
      constructor
      · rintro ⟨D, hD, hw⟩
        by_cases hDC : D = C
        · exact Or.inl (hDC ▸ hw)
        · exact Or.inr ⟨D, ⟨hDC, hD⟩, hw⟩
      · rintro (hw | ⟨D, ⟨-, hD⟩, hw⟩)
        · exact ⟨C, hC, hw⟩
        · exact ⟨D, hD, hw⟩
    have hrestC : ∀ C' ∈ 𝒞.erase C, ∀ w, w ∈ C' → w ∉ C := by
      intro C' hC' w hw hwC
      have := hdis C hC C' (Finset.mem_of_mem_erase hC') (Ne.symm (Finset.ne_of_mem_erase hC'))
      exact Finset.disjoint_left.mp this hwC hw
    have hrestdis : ∀ C₁ ∈ 𝒞.erase C, ∀ C₂ ∈ 𝒞.erase C, C₁ ≠ C₂ → Disjoint C₁ C₂ :=
      fun C₁ h₁ C₂ h₂ => hdis C₁ (Finset.mem_of_mem_erase h₁) C₂ (Finset.mem_of_mem_erase h₂)
    have hfilter : ∀ (α₁ β₁ : E → W),
        (∀ C' ∈ 𝒞.erase C, (epCut α₁ β₁ C').card = (epCut α β C').card) →
        ((𝒞.erase C).filter (fun C' => (epCut α₁ β₁ C').card = 3)).card =
          ((𝒞.erase C).filter (fun C' => (epCut α β C').card = 3)).card := by
      intro α₁ β₁ hcard
      congr 1
      exact Finset.filter_congr (fun C' hC' => by rw [hcard C' hC'])
    have hCnot : C ∉ 𝒞.erase C := Finset.notMem_erase C 𝒞
    have hins : 𝒞 = insert C (𝒞.erase C) := (Finset.insert_erase hC).symm
    have hRC : ∀ w, w ∈ L \ 𝒞.biUnion id → w ∉ C := fun w hw h' =>
      (Finset.mem_sdiff.mp hw).2 (by rw [hU]; exact Finset.mem_union_left _ h')
    rcases hCcut with h2 | h3
    · -- a 2-cut: contraction by redirection
      obtain ⟨e, e', hee', hcutset⟩ := Finset.card_eq_two.mp h2
      have hcut : ∀ g, epCross α β C g ↔ g = e ∨ g = e' := by
        intro g; rw [← mem_epCut, hcutset, Finset.mem_insert, Finset.mem_singleton]
      obtain ⟨x₁, hx₁⟩ := hCne
      have hstep : EpStep α β L (ep2A α β C e e' x₁) (ep2B α β C e e' x₁) (L \ C) :=
        Or.inr ⟨C, e, e', x₁, hCL, hx₁, hee', hcut, rfl, rfl, rfl⟩
      obtain ⟨h₁, hb₁, hconn₁, -, -⟩ := hstep.preserves h hb hconn
      have hcard₁ : ∀ C' ∈ 𝒞.erase C,
          (epCut (ep2A α β C e e' x₁) (ep2B α β C e e' x₁) C').card = (epCut α β C').card := by
        intro C' hC'
        obtain ⟨a1, a2, a3, a4⟩ := h𝒞 C' (Finset.mem_of_mem_erase hC')
        refine ep2_cut_card_other α β C C' e e' x₁ (hrestC C' hC') hee' hcut ?_
        exact ep_two_cut_not_both α β L C C' e e' r h hb hconn hCL a1
          (fun w hw hw' => hrestC C' hC' w hw' hw) hr hrC a3 hee' hcut (by omega)
      obtain ⟨α', β', L', newE, hreach, hsub, hsubL, hcardL, hfix, hburl, hlift⟩ :=
        ih (ep2A α β C e e' x₁) (ep2B α β C e e' x₁) (L \ C) (𝒞.erase C) r hrest_card h₁ hb₁
          hconn₁ (Finset.mem_sdiff.mpr ⟨hr, hrC⟩)
          (fun C' hC' => by
            obtain ⟨a1, a2, a3, a4⟩ := h𝒞 C' (Finset.mem_of_mem_erase hC')
            refine ⟨fun w hw => Finset.mem_sdiff.mpr ⟨a1 hw, hrestC C' hC' w hw⟩, a2, a3, ?_⟩
            rw [hcard₁ C' hC']; exact a4)
          hrestdis
      have hUeq : (L \ C) \ (𝒞.erase C).biUnion id = L \ 𝒞.biUnion id := by
        rw [hU]; ext w; simp only [Finset.mem_sdiff, Finset.mem_union]; tauto
      rw [hUeq] at hsub hcardL hfix hburl hlift
      have hfix₁ : ∀ g, α g ∈ L \ 𝒞.biUnion id → β g ∈ L \ 𝒞.biUnion id →
          ep2A α β C e e' x₁ g = α g ∧ ep2B α β C e e' x₁ g = β g := by
        intro g ha hb'
        have haC : α g ∉ C := fun h' => (Finset.mem_sdiff.mp ha).2 (by rw [hU]; exact Finset.mem_union_left _ h')
        have hbC : β g ∉ C := fun h' => (Finset.mem_sdiff.mp hb').2 (by rw [hU]; exact Finset.mem_union_left _ h')
        have hnc : ¬epCross α β C g := by unfold epCross; tauto
        have hge : g ≠ e := fun h' => hnc ((hcut g).mpr (Or.inl h'))
        have hge' : g ≠ e' := fun h' => hnc ((hcut g).mpr (Or.inr h'))
        unfold ep2A ep2B
        rw [if_neg hge, if_neg hge, if_neg (fun h' => h'.elim hge' (fun h'' => haC h''.1)),
          if_neg (fun h' => h'.elim hge' (fun h'' => haC h''.1))]
        exact ⟨rfl, rfl⟩
      refine ⟨α', β', L', insert e newE, Relation.ReflTransGen.head hstep hreach, hsub,
        hsubL.trans Finset.sdiff_subset, ?_, ?_, ?_, ?_⟩
      · rw [hcardL, hfilter _ _ hcard₁]
        congr 1
        rw [hins, Finset.filter_insert, if_neg (by omega), Finset.erase_insert hCnot]
      · intro g ha hb'
        obtain ⟨c1, c2⟩ := hfix₁ g ha hb'
        obtain ⟨d1, d2⟩ := hfix g (c1 ▸ ha) (c2 ▸ hb')
        exact ⟨d1.trans c1, d2.trans c2⟩
      · intro Z hZ hnew hZburl
        obtain ⟨hb1, hc1⟩ := hburl Z hZ (fun g hg => hnew g (Finset.mem_insert_of_mem hg)) hZburl
        have hZL : Z ⊆ L := fun w hw => (Finset.mem_sdiff.mp (hZ hw)).1
        have hZC : ∀ w, w ∈ Z → w ∉ C := fun w hw h' =>
          (Finset.mem_sdiff.mp (hZ hw)).2 (by rw [hU]; exact Finset.mem_union_left _ h')
        have hnewe : ¬(epOut α β C e ∈ Z ∧ epOut α β C e' ∈ Z) := by
          rintro ⟨ha, ha'⟩
          have hA : ep2A α β C e e' x₁ e = epOut α β C e := by unfold ep2A; rw [if_pos rfl]
          have hB : ep2B α β C e e' x₁ e = epOut α β C e' := by unfold ep2B; rw [if_pos rfl]
          obtain ⟨d1, d2⟩ := hfix e (hA ▸ hZ ha) (hB ▸ hZ ha')
          apply hnew e (Finset.mem_insert_self _ _)
          rw [d1, d2, hA, hB]; exact ⟨ha, ha'⟩
        obtain ⟨hb2, hc2⟩ := ep2_burl α β L C Z e e' x₁ h hx₁ hee' hcut hZL hZC hnewe hb1
        exact ⟨hb2, hc2.trans hc1⟩
      · intro T' hT'
        obtain ⟨Z₁, hZ₁L, i1, i2, i3, i4, i5⟩ := hlift T' hT'
        have hZ₁C : ∀ w, w ∈ Z₁ → w ∉ C := fun w hw => (Finset.mem_sdiff.mp (hZ₁L hw)).2
        have hZdef : ∀ w, w ∈ ep2Lift C (epOut α β C e') Z₁ ↔
            w ∈ Z₁ ∨ (epOut α β C e' ∈ Z₁ ∧ w ∈ C) := by
          intro w; unfold ep2Lift
          by_cases ho : epOut α β C e' ∈ Z₁
          · rw [if_pos ho, Finset.mem_union]; tauto
          · rw [if_neg ho]; tauto
        obtain ⟨j1, j2, j3, j4⟩ := ep_lift_book 𝒞 C (L \ 𝒞.biUnion id) (L \ 𝒞.biUnion id) T' L'
          (ep2Lift C (epOut α β C e') Z₁) Z₁ x₁ hrestC hC (Finset.Subset.refl _)
          (Finset.subset_insert _ _) hRC
          (fun w hw => by rw [hZdef]; exact ⟨fun h' => h'.elim id (fun h'' => absurd h''.2 hw),
            Or.inl⟩)
          (by
            by_cases ho : epOut α β C e' ∈ Z₁
            · exact Or.inl (fun w hw => (hZdef w).mpr (Or.inr ⟨ho, hw⟩))
            · right; rw [Finset.disjoint_left]; intro w hw hwZ
              rcases (hZdef w).mp hwZ with h' | h'
              · exact hZ₁C w h' hw
              · exact ho h'.1)
          (fun h' => absurd hx₁ (hRC x₁ h')) (fun h' => absurd hx₁ (hRC x₁ h')) i1 i2 i4 i5
        refine ⟨_, ?_, j1, j2, ?_, j3, j4⟩
        · intro w hw
          rcases (hZdef w).mp hw with h' | h'
          · exact (Finset.mem_sdiff.mp (hZ₁L h')).1
          · exact hCL h'.2
        · rw [← i3, ep2_cut α β C e e' x₁ hcut Z₁ hZ₁C]
    · -- a 3-cut
      by_cases hC1 : C.card = 1
      · -- a single vertex: nothing to contract
        obtain ⟨α', β', L', newE, hreach, hsub, hsubL, hcardL, hfix, hburl, hlift⟩ :=
          ih α β L (𝒞.erase C) r hrest_card h hb hconn hr
            (fun C' hC' => h𝒞 C' (Finset.mem_of_mem_erase hC')) hrestdis
        have hsubU : L \ 𝒞.biUnion id ⊆ L \ (𝒞.erase C).biUnion id := by
          rw [hU]; intro w; simp only [Finset.mem_sdiff, Finset.mem_union]; tauto
        refine ⟨α', β', L', newE, hreach, hsubU.trans hsub, hsubL, ?_,
          fun g ha hb' => hfix g (hsubU ha) (hsubU hb'),
          fun Z hZ hnew hZb => hburl Z (hZ.trans hsubU) hnew hZb, fun T' hT' => ?_⟩
        rw [hcardL]
        have hsplit : L \ (𝒞.erase C).biUnion id = (L \ 𝒞.biUnion id) ∪ C := by
          rw [hU]; ext w
          simp only [Finset.mem_sdiff, Finset.mem_union]
          constructor
          · rintro ⟨h1, h2⟩
            by_cases hwC : w ∈ C
            · exact Or.inr hwC
            · exact Or.inl ⟨h1, fun h' => h'.elim hwC h2⟩
          · rintro (⟨h1, h2⟩ | h1)
            · exact ⟨h1, fun h' => h2 (Or.inr h')⟩
            · refine ⟨hCL h1, ?_⟩
              simp only [Finset.mem_biUnion, id]
              rintro ⟨D, hD, hwD⟩
              exact hrestC D hD w hwD h1
        have hdj : Disjoint (L \ 𝒞.biUnion id) C := by
          rw [Finset.disjoint_left]; intro w hw hwC
          exact (Finset.mem_sdiff.mp hw).2 (by rw [hU]; exact Finset.mem_union_left _ hwC)
        rw [hsplit, Finset.card_union_of_disjoint hdj, hC1]
        have hf : 𝒞.filter (fun C' => (epCut α β C').card = 3) =
            insert C ((𝒞.erase C).filter (fun C' => (epCut α β C').card = 3)) := by
          conv_lhs => rw [hins]
          rw [Finset.filter_insert, if_pos h3]
        rw [hf, Finset.card_insert_of_notMem (fun h' => hCnot (Finset.mem_of_mem_filter _ h'))]
        omega
        obtain ⟨Z₁, hZ₁L, i1, i2, i3, i4, i5⟩ := hlift T' hT'
        obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hC1
        obtain ⟨j1, j2, j3, j4⟩ := ep_lift_book 𝒞 C (L \ 𝒞.biUnion id)
          (L \ (𝒞.erase C).biUnion id) T' L' Z₁ Z₁ v hrestC hC hsubU
          (fun w hw => by
            by_cases hwC : w ∈ C
            · rw [hv, Finset.mem_singleton] at hwC
              exact Finset.mem_insert.mpr (Or.inl hwC)
            · refine Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr
                ⟨(Finset.mem_sdiff.mp hw).1, ?_⟩)
              rw [hU, Finset.mem_union]
              exact fun h' => h'.elim hwC (Finset.mem_sdiff.mp hw).2)
          hRC (fun _ _ => Iff.rfl)
          (by
            rw [hv]
            by_cases hvZ : v ∈ Z₁
            · exact Or.inl (Finset.singleton_subset_iff.mpr hvZ)
            · exact Or.inr (Finset.disjoint_singleton_left.mpr hvZ))
          (fun _ h' => by rw [hv]; exact Finset.singleton_subset_iff.mpr h')
          (fun _ h' => by rw [hv]; exact Finset.disjoint_singleton_left.mpr h') i1 i2 i4 i5
        exact ⟨Z₁, hZ₁L, j1, j2, i3, j3, j4⟩
      · obtain ⟨x₀, hx₀, x₁, hx₁, hx⟩ := Finset.one_lt_card.mp (by
          have := Finset.card_pos.mpr hCne; omega : 1 < C.card)
        have hstep : EpStep α β L (epConA α β C x₀ x₁) (epConB α β C x₀ x₁) (epL' L C x₀) :=
          Or.inl ⟨C, x₀, x₁, hCL, hx₀, hx₁, hx.symm, h3, rfl, rfl, rfl⟩
        obtain ⟨h₁, hb₁, hconn₁, -, -⟩ := hstep.preserves h hb hconn
        have hsubL₁ : ∀ C' ∈ 𝒞.erase C, C' ⊆ epL' L C x₀ := by
          intro C' hC' w hw
          unfold epL'
          exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr
            ⟨(h𝒞 C' (Finset.mem_of_mem_erase hC')).1 hw, hrestC C' hC' w hw⟩)
        have hcard₁ : ∀ C' ∈ 𝒞.erase C,
            (epCut (epConA α β C x₀ x₁) (epConB α β C x₀ x₁) C').card = (epCut α β C').card := by
          intro C' hC'
          rw [epCon_cut α β L C x₀ x₁ hx₀ C' (hsubL₁ C' hC')]
          unfold epLift
          rw [if_neg (fun h' => hrestC C' hC' x₀ h' hx₀)]
        have hr₁ : r ∈ epL' L C x₀ := by
          unfold epL'; exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨hr, hrC⟩)
        obtain ⟨α', β', L', newE, hreach, hsub, hsubL, hcardL, hfix, hburl, hlift⟩ :=
          ih (epConA α β C x₀ x₁) (epConB α β C x₀ x₁) (epL' L C x₀) (𝒞.erase C) r hrest_card
            h₁ hb₁ hconn₁ hr₁
            (fun C' hC' => by
              obtain ⟨a1, a2, a3, a4⟩ := h𝒞 C' (Finset.mem_of_mem_erase hC')
              refine ⟨hsubL₁ C' hC', a2, a3, ?_⟩
              rw [hcard₁ C' hC']; exact a4)
            hrestdis
        have hx₀rest : x₀ ∉ (𝒞.erase C).biUnion id := by
          simp only [Finset.mem_biUnion, id]
          rintro ⟨D, hD, hwD⟩
          exact hrestC D hD x₀ hwD hx₀
        have hUeq : epL' L C x₀ \ (𝒞.erase C).biUnion id = insert x₀ (L \ 𝒞.biUnion id) := by
          rw [hU]; unfold epL'; ext w
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_union]
          constructor
          · rintro ⟨h1 | h1, h2⟩
            · exact Or.inl h1
            · exact Or.inr ⟨h1.1, fun h' => h'.elim h1.2 h2⟩
          · rintro (h1 | ⟨h1, h2⟩)
            · exact ⟨Or.inl h1, h1 ▸ hx₀rest⟩
            · exact ⟨Or.inr ⟨h1, fun h' => h2 (Or.inl h')⟩, fun h' => h2 (Or.inr h')⟩
        rw [hUeq] at hsub hcardL hfix hburl hlift
        have hx₀U : x₀ ∉ L \ 𝒞.biUnion id := fun h' =>
          (Finset.mem_sdiff.mp h').2 (by rw [hU]; exact Finset.mem_union_left _ hx₀)
        have hsubU : L \ 𝒞.biUnion id ⊆ insert x₀ (L \ 𝒞.biUnion id) := Finset.subset_insert _ _
        have hfix₁ : ∀ g, α g ∈ L \ 𝒞.biUnion id → β g ∈ L \ 𝒞.biUnion id →
            epConA α β C x₀ x₁ g = α g ∧ epConB α β C x₀ x₁ g = β g := by
          intro g ha hb'
          have haC : α g ∉ C := fun h' =>
            (Finset.mem_sdiff.mp ha).2 (by rw [hU]; exact Finset.mem_union_left _ h')
          have hbC : β g ∉ C := fun h' =>
            (Finset.mem_sdiff.mp hb').2 (by rw [hU]; exact Finset.mem_union_left _ h')
          have hin : ¬(α g ∈ C ∧ β g ∈ C) := fun h' => haC h'.1
          unfold epConA epConB epRho
          rw [if_neg hin, if_neg hin, if_neg haC, if_neg hbC]
          exact ⟨rfl, rfl⟩
        refine ⟨α', β', L', newE, Relation.ReflTransGen.head hstep hreach, hsubU.trans hsub, ?_,
          ?_, ?_, ?_, ?_⟩
        · intro w hw
          have := hsubL hw
          unfold epL' at this
          rw [Finset.mem_insert, Finset.mem_sdiff] at this
          rcases this with rfl | ⟨h1, -⟩
          · exact hCL hx₀
          · exact h1
        · rw [hcardL, Finset.card_insert_of_notMem hx₀U, hfilter _ _ hcard₁]
          have hf : 𝒞.filter (fun C' => (epCut α β C').card = 3) =
              insert C ((𝒞.erase C).filter (fun C' => (epCut α β C').card = 3)) := by
            conv_lhs => rw [hins]
            rw [Finset.filter_insert, if_pos h3]
          rw [hf, Finset.card_insert_of_notMem (fun h' => hCnot (Finset.mem_of_mem_filter _ h'))]
          omega
        · intro g ha hb'
          obtain ⟨c1, c2⟩ := hfix₁ g ha hb'
          obtain ⟨d1, d2⟩ := hfix g (c1 ▸ hsubU ha) (c2 ▸ hsubU hb')
          exact ⟨d1.trans c1, d2.trans c2⟩
        · intro Z hZ hnew hZburl
          obtain ⟨hb1, hc1⟩ := hburl Z (hZ.trans hsubU) hnew hZburl
          have hZL : Z ⊆ L := fun w hw => (Finset.mem_sdiff.mp (hZ hw)).1
          have hZC : ∀ w, w ∈ Z → w ∉ C := fun w hw h' =>
            (Finset.mem_sdiff.mp (hZ hw)).2 (by rw [hU]; exact Finset.mem_union_left _ h')
          obtain ⟨hb2, hc2⟩ := epCon_burl α β L C Z x₀ x₁ h hCL hx₀ hx₁ hZL hZC hb1
          exact ⟨hb2, hc2.trans hc1⟩
        · intro T' hT'
          obtain ⟨Z₁, hZ₁L, i1, i2, i3, i4, i5⟩ := hlift T' hT'
          have hZdef : ∀ w, w ∈ epLift C x₀ Z₁ ↔ w ∈ Z₁ ∨ (x₀ ∈ Z₁ ∧ w ∈ C) := by
            intro w; unfold epLift
            by_cases ho : x₀ ∈ Z₁
            · rw [if_pos ho, Finset.mem_union]; tauto
            · rw [if_neg ho]; tauto
          have hZ₁C : ∀ w, w ∈ Z₁ → w ∈ C → w = x₀ := by
            intro w hw hwC
            have := hZ₁L hw
            unfold epL' at this
            rcases Finset.mem_insert.mp this with h' | h'
            · exact h'
            · exact absurd hwC (Finset.mem_sdiff.mp h').2
          have hdj : x₀ ∉ Z₁ → Disjoint C (epLift C x₀ Z₁) := by
            intro ho
            rw [Finset.disjoint_left]; intro w hw hwZ
            rcases (hZdef w).mp hwZ with h' | h'
            · exact ho (by rw [← hZ₁C w h' hw]; exact h')
            · exact ho h'.1
          obtain ⟨j1, j2, j3, j4⟩ := ep_lift_book 𝒞 C (L \ 𝒞.biUnion id)
            (insert x₀ (L \ 𝒞.biUnion id)) T' L' (epLift C x₀ Z₁) Z₁ x₀ hrestC hC hsubU
            (Finset.Subset.refl _) hRC
            (fun w hw => by rw [hZdef]; exact ⟨fun h' => h'.elim id (fun h'' => absurd h''.2 hw),
              Or.inl⟩)
            (by
              by_cases ho : x₀ ∈ Z₁
              · exact Or.inl (fun w hw => (hZdef w).mpr (Or.inr ⟨ho, hw⟩))
              · exact Or.inr (hdj ho))
            (fun _ h' w hw => (hZdef w).mpr (Or.inr ⟨h', hw⟩)) (fun _ h' => hdj h') i1 i2 i4 i5
          refine ⟨_, ?_, j1, j2, ?_, j3, j4⟩
          · intro w hw
            rcases (hZdef w).mp hw with h' | h'
            · have := hZ₁L h'
              unfold epL' at this
              rcases Finset.mem_insert.mp this with h'' | h''
              · rw [h'']; exact hCL hx₀
              · exact (Finset.mem_sdiff.mp h'').1
            · exact hCL h'.2
          · rw [← i3, epCon_cut α β L C x₀ x₁ hx₀ Z₁ hZ₁L]

/-- In a family of pairwise disjoint nonempty sets, every member is a leaf whose atom is the
member itself. -/
lemma ep_flat_leaf {W : Type*} [DecidableEq W] (𝒮 : Finset (Finset W))
    (hne : ∀ S ∈ 𝒮, S.Nonempty) (hdis : ∀ S ∈ 𝒮, ∀ S' ∈ 𝒮, S ≠ S' → Disjoint S S')
    (S : Finset W) (hS : S ∈ 𝒮) : epChildren 𝒮 S = ∅ ∧ epAtom 𝒮 S = S := by
  have hno : ∀ C ∈ 𝒮, ¬C ⊂ S := by
    intro C hC hCS
    obtain ⟨w, hw⟩ := hne C hC
    have hd := hdis C hC S hS (fun h' => hCS.2 (h' ▸ Finset.Subset.refl _))
    exact Finset.disjoint_left.mp hd hw (hCS.1 hw)
  constructor
  · unfold epChildren
    rw [Finset.filter_eq_empty_iff]
    intro C hC h'
    exact hno C hC h'.1
  · ext w
    rw [mem_epAtom]
    exact ⟨fun h' => h'.1, fun h' => ⟨h', fun C hC hCS => absurd hCS (hno C hC)⟩⟩

/-- In a family of pairwise disjoint nonempty proper subsets of `L`, the children of the root
are all members, and the atom of the root is the complement of their union. -/
lemma ep_flat_root {W : Type*} [DecidableEq W] (𝒮 : Finset (Finset W)) (L : Finset W)
    (hne : ∀ S ∈ 𝒮, S.Nonempty) (hsub : ∀ S ∈ 𝒮, S ⊂ L)
    (hdis : ∀ S ∈ 𝒮, ∀ S' ∈ 𝒮, S ≠ S' → Disjoint S S') :
    epChildren 𝒮 L = 𝒮 ∧ epAtom 𝒮 L = L \ 𝒮.biUnion id := by
  constructor
  · unfold epChildren
    rw [Finset.filter_eq_self]
    intro C hC
    refine ⟨hsub C hC, fun D hD hCD _ => ?_⟩
    obtain ⟨w, hw⟩ := hne C hC
    have hd := hdis C hC D hD (fun h' => hCD.2 (h' ▸ Finset.Subset.refl _))
    exact Finset.disjoint_left.mp hd hw (hCD.1 hw)
  · ext w
    rw [mem_epAtom, Finset.mem_sdiff, Finset.mem_biUnion]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun ⟨C, hC, hwC⟩ => h2 C hC (hsub C hC) hwC⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun C hC _ hwC => h2 ⟨C, hC, hwC⟩⟩

open Classical in
/-- **Existence of decompositions, flat case.** A family of pairwise disjoint sets with at least
two vertices each, cuts of size two or three, none containing the root vertex, is a
decomposition as soon as the root node satisfies the node condition. -/
theorem ep_flat_decomp {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (r : W)
    (𝒮 : Finset (Finset W)) (hr : r ∈ L)
    (hmem : ∀ S ∈ 𝒮, S ⊆ L ∧ 2 ≤ S.card ∧ r ∉ S ∧
      ((epCut α β S).card = 2 ∨ (epCut α β S).card = 3))
    (hdis : ∀ S ∈ 𝒮, ∀ S' ∈ 𝒮, S ≠ S' → Disjoint S S')
    (hroot : 3 ≤ (L \ 𝒮.biUnion id).card + 𝒮.card) :
    EpDecomp α β L r 𝒮 ∧ ∀ S ∈ 𝒮, epChildren 𝒮 S = ∅ := by
  have hne : ∀ S ∈ 𝒮, S.Nonempty := fun S hS =>
    Finset.card_pos.mp (by have := (hmem S hS).2.1; omega)
  have hsub : ∀ S ∈ 𝒮, S ⊂ L := fun S hS =>
    Finset.ssubset_iff_subset_ne.mpr ⟨(hmem S hS).1, fun h' => (hmem S hS).2.2.1 (h' ▸ hr)⟩
  have hLnot : L ∉ 𝒮 := fun h' => (hsub L h').2 (Finset.Subset.refl _)
  refine ⟨⟨fun S hS S' hS' => ?_, fun S hS => ⟨(hmem S hS).1, hne S hS, (hmem S hS).2.2.1,
    (hmem S hS).2.2.2⟩, fun N hN => ?_⟩, fun S hS => (ep_flat_leaf 𝒮 hne hdis S hS).1⟩
  · by_cases h' : S = S'
    · exact Or.inl (h' ▸ Finset.Subset.refl _)
    · exact Or.inr (Or.inr (hdis S hS S' hS' h'))
  · rcases Finset.mem_insert.mp hN with rfl | hN'
    · obtain ⟨h1, h2⟩ := ep_flat_root 𝒮 N hne hsub hdis
      rw [h1, h2, if_pos rfl]; omega
    · obtain ⟨h1, h2⟩ := ep_flat_leaf 𝒮 hne hdis N hN'
      have hNL : ¬(N = L) := fun h' => hLnot (h' ▸ hN')
      rw [h1, h2, if_neg hNL, Finset.card_empty]
      have := (hmem N hN').2.1
      omega

open Classical in
/-- **Existence of decompositions, one cut.** A set `X` with a cut of size two or three and at
least two vertices on each side gives a decomposition with a single member: the side of the cut
that does not contain the root vertex. -/
theorem ep_single_decomp {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (r : W)
    (h : EpCubicD α β L) (X : Finset W) (hr : r ∈ L) (hXL : X ⊆ L) (hX2 : 2 ≤ X.card)
    (hY2 : 2 ≤ (L \ X).card)
    (hcut : (epCut α β X).card = 2 ∨ (epCut α β X).card = 3) :
    (r ∉ X → EpDecomp α β L r {X} ∧ epChildren {X} X = ∅) ∧
      (r ∈ X → EpDecomp α β L r {L \ X} ∧ epAtom {L \ X} L = X ∧
        (epChildren {L \ X} L).card = 1) := by
  have hcutY : (epCut α β (L \ X)).card = (epCut α β X).card := by
    have : epCut α β (L \ X) = epCut α β X := by
      ext g; rw [mem_epCut, mem_epCut]
      exact epD_cross_compl α β L X (L \ X) h (fun w => Finset.mem_sdiff) g
    rw [this]
  have hsd : L \ (L \ X) = X := by
    ext w; simp only [Finset.mem_sdiff]
    constructor
    · rintro ⟨h1, h2⟩; by_contra h'; exact h2 ⟨h1, h'⟩
    · intro hw; exact ⟨hXL hw, fun h' => h'.2 hw⟩
  constructor
  · intro hrX
    have := ep_flat_decomp α β L r {X} hr
      (fun S hS => by rw [Finset.mem_singleton.mp hS]; exact ⟨hXL, hX2, hrX, hcut⟩)
      (fun S hS S' hS' hne => absurd ((Finset.mem_singleton.mp hS).trans
        (Finset.mem_singleton.mp hS').symm) hne)
      (by rw [Finset.singleton_biUnion, Finset.card_singleton]; simp only [id]; omega)
    exact ⟨this.1, this.2 X (Finset.mem_singleton_self X)⟩
  · intro hrX
    have hrY : r ∉ L \ X := fun h' => (Finset.mem_sdiff.mp h').2 hrX
    have hd := ep_flat_decomp α β L r {L \ X} hr
      (fun S hS => by
        rw [Finset.mem_singleton.mp hS]
        exact ⟨Finset.sdiff_subset, hY2, hrY, by rw [hcutY]; exact hcut⟩)
      (fun S hS S' hS' hne => absurd ((Finset.mem_singleton.mp hS).trans
        (Finset.mem_singleton.mp hS').symm) hne)
      (by rw [Finset.singleton_biUnion, Finset.card_singleton]; simp only [id]; rw [hsd]; omega)
    have hroot := ep_flat_root ({L \ X} : Finset (Finset W)) L
      (fun S hS => by
        rw [Finset.mem_singleton.mp hS]; exact Finset.card_pos.mp (by omega))
      (fun S hS => by
        rw [Finset.mem_singleton.mp hS]
        exact Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset,
          fun h' => hrY (by rw [h']; exact hr)⟩)
      (fun S hS S' hS' hne => absurd ((Finset.mem_singleton.mp hS).trans
        (Finset.mem_singleton.mp hS').symm) hne)
    refine ⟨hd.1, ?_, ?_⟩
    · rw [hroot.2, Finset.singleton_biUnion]; simp only [id]; exact hsd
    · rw [hroot.1, Finset.card_singleton]

open Classical in
/-- **Existence of decompositions, case `𝒴 = ∅`** (the graph is not cyclically
4-edge-connected). -/
theorem ep_decomp_exists_empty {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (r : W)
    (h : EpCubicD α β L) (hb : EpBridgeless α β L) (hconn : EpConnected α β L) (hr : r ∈ L)
    (h4 : ¬EpCyc4 α β L) : ∃ 𝒮, EpDecomp α β L r 𝒮 ∧ EpRefines L r 𝒮 ∅ := by
  have key : ∃ X, X ⊆ L ∧ 2 ≤ X.card ∧ 2 ≤ (L \ X).card ∧
      ((epCut α β X).card = 2 ∨ (epCut α β X).card = 3) := by
    rcases epD_cut_trichotomy α β L h hb hconn with h4' | ⟨X, e, e', hXL, hXne, hXL', hee', hcut⟩ |
      ⟨X, hXL, h3, hX3, hY3⟩
    · exact absurd h4' h4
    · have hc2 : (epCut α β X).card = 2 := by
        have : epCut α β X = {e, e'} := by
          ext g; rw [mem_epCut, hcut, Finset.mem_insert, Finset.mem_singleton]
        rw [this, Finset.card_pair hee']
      have hpX := epD_cut_parity α β L h X hXL
      have hpL := epD_cut_parity α β L h L (Finset.Subset.refl L)
      have hcutL : epCut α β L = ∅ := by
        ext g
        rw [mem_epCut]
        simp only [Finset.notMem_empty, iff_false]
        intro hc
        have := epD_live_of_cross h L g hc
        unfold epCross at hc; tauto
      rw [hcutL, Finset.card_empty] at hpL
      rw [hc2] at hpX
      have hXpos := Finset.card_pos.mpr hXne
      have hsd : (L \ X).card = L.card - X.card := Finset.card_sdiff_of_subset hXL
      have hlt : X.card < L.card :=
        Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hXL, hXL'⟩)
      exact ⟨X, hXL, by omega, by omega, Or.inl hc2⟩
    · exact ⟨X, hXL, by omega, by omega, Or.inr h3⟩
  obtain ⟨X, hXL, hX2, hY2, hcut⟩ := key
  obtain ⟨h1, h2⟩ := ep_single_decomp α β L r h X hr hXL hX2 hY2 hcut
  by_cases hrX : r ∈ X
  · exact ⟨{L \ X}, (h2 hrX).1, fun Y hY => absurd hY (Finset.notMem_empty Y)⟩
  · exact ⟨{X}, (h1 hrX).1, fun Y hY => absurd hY (Finset.notMem_empty Y)⟩

open Classical in
/-- **Existence of decompositions, case `𝒴 = {Y}`.** -/
theorem ep_decomp_exists_single {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (r : W)
    (h : EpCubicD α β L) (hr : r ∈ L) (Y : Finset W) (hYL : Y ⊆ L) (hY2 : 2 ≤ Y.card)
    (hYc : 2 ≤ (L \ Y).card) (hcut : (epCut α β Y).card = 2 ∨ (epCut α β Y).card = 3) :
    ∃ 𝒮, EpDecomp α β L r 𝒮 ∧ EpRefines L r 𝒮 {Y} := by
  obtain ⟨h1, h2⟩ := ep_single_decomp α β L r h Y hr hYL hY2 hYc hcut
  by_cases hrY : r ∈ Y
  · obtain ⟨a1, a2, a3⟩ := h2 hrY
    refine ⟨{L \ Y}, a1, fun Y' hY' => ?_⟩
    rw [Finset.mem_singleton.mp hY']
    exact Or.inr ⟨hrY, a2.symm, a3⟩
  · obtain ⟨a1, a2⟩ := h1 hrY
    refine ⟨{Y}, a1, fun Y' hY' => ?_⟩
    rw [Finset.mem_singleton.mp hY']
    exact Or.inl ⟨Finset.mem_singleton_self Y, a2⟩

open Classical in
/-- **Existence of decompositions, case `|𝒴| ≥ 2` with the root outside `⋃ 𝒴`.** -/
theorem ep_decomp_exists_flat {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (r : W)
    (hr : r ∈ L) (𝒴 : Finset (Finset W)) (h2 : 2 ≤ 𝒴.card)
    (hmem : ∀ Y ∈ 𝒴, Y ⊆ L ∧ 2 ≤ Y.card ∧ r ∉ Y ∧
      ((epCut α β Y).card = 2 ∨ (epCut α β Y).card = 3))
    (hdis : ∀ Y ∈ 𝒴, ∀ Y' ∈ 𝒴, Y ≠ Y' → Disjoint Y Y') :
    EpDecomp α β L r 𝒴 ∧ EpRefines L r 𝒴 𝒴 := by
  have hpos : 1 ≤ (L \ 𝒴.biUnion id).card := by
    refine Finset.card_pos.mpr ⟨r, Finset.mem_sdiff.mpr ⟨hr, ?_⟩⟩
    simp only [Finset.mem_biUnion, id]
    rintro ⟨Y, hY, hrY⟩
    exact (hmem Y hY).2.2.1 hrY
  have hd := ep_flat_decomp α β L r 𝒴 hr hmem hdis (by omega)
  exact ⟨hd.1, fun Y hY => Or.inl ⟨hY, hd.2 Y hY⟩⟩

set_option maxHeartbeats 1600000 in
open Classical in
/-- **Existence of decompositions, case `|𝒴| ≥ 2` with the root inside a member `Y₀` of `𝒴`.**
The decomposition consists of `L \ Y₀` and the other members of `𝒴`. -/
theorem ep_decomp_exists_rooted {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (r : W)
    (h : EpCubicD α β L) (hr : r ∈ L) (𝒴 : Finset (Finset W)) (Y₀ : Finset W) (hY₀ : Y₀ ∈ 𝒴)
    (hrY₀ : r ∈ Y₀) (h2 : 2 ≤ 𝒴.card)
    (hmem : ∀ Y ∈ 𝒴, Y ⊆ L ∧ 2 ≤ Y.card ∧
      ((epCut α β Y).card = 2 ∨ (epCut α β Y).card = 3))
    (hdis : ∀ Y ∈ 𝒴, ∀ Y' ∈ 𝒴, Y ≠ Y' → Disjoint Y Y') :
    ∃ 𝒮, EpDecomp α β L r 𝒮 ∧ EpRefines L r 𝒮 𝒴 := by
  obtain ⟨hY₀L, hY₀2, hY₀cut⟩ := hmem Y₀ hY₀
  have hRne : (𝒴.erase Y₀).Nonempty := Finset.card_pos.mp (by
    rw [Finset.card_erase_of_mem hY₀]; omega)
  have hRsub : ∀ R ∈ 𝒴.erase Y₀, R ⊆ L \ Y₀ := by
    intro R hR w hw
    have hd := hdis R (Finset.mem_of_mem_erase hR) Y₀ hY₀ (Finset.ne_of_mem_erase hR)
    exact Finset.mem_sdiff.mpr ⟨(hmem R (Finset.mem_of_mem_erase hR)).1 hw,
      Finset.disjoint_left.mp hd hw⟩
  have hRr : ∀ R ∈ 𝒴.erase Y₀, r ∉ R := fun R hR h' =>
    (Finset.mem_sdiff.mp (hRsub R hR h')).2 hrY₀
  have hRne' : ∀ R ∈ 𝒴.erase Y₀, R.Nonempty := fun R hR =>
    Finset.card_pos.mp (by have := (hmem R (Finset.mem_of_mem_erase hR)).2.1; omega)
  have hRdis : ∀ R ∈ 𝒴.erase Y₀, ∀ R' ∈ 𝒴.erase Y₀, R ≠ R' → Disjoint R R' :=
    fun R hR R' hR' => hdis R (Finset.mem_of_mem_erase hR) R' (Finset.mem_of_mem_erase hR')
  have hsd : L \ (L \ Y₀) = Y₀ := by
    ext w; simp only [Finset.mem_sdiff]
    constructor
    · rintro ⟨h1, h2'⟩; by_contra h'; exact h2' ⟨h1, h'⟩
    · intro hw; exact ⟨hY₀L hw, fun h' => h'.2 hw⟩
  have hrP : r ∉ L \ Y₀ := fun h' => (Finset.mem_sdiff.mp h').2 hrY₀
  by_cases hP : L \ Y₀ ∈ 𝒴.erase Y₀
  · -- then the other member is the complement of `Y₀`
    have hYc : 2 ≤ (L \ Y₀).card := (hmem _ (Finset.mem_of_mem_erase hP)).2.1
    obtain ⟨-, hs2⟩ := ep_single_decomp α β L r h Y₀ hr hY₀L hY₀2 hYc hY₀cut
    obtain ⟨a1, a2, a3⟩ := hs2 hrY₀
    refine ⟨{L \ Y₀}, a1, fun Y hY => ?_⟩
    by_cases hYY : Y = Y₀
    · rw [hYY]; exact Or.inr ⟨hrY₀, a2.symm, a3⟩
    · left
      have hYR : Y ∈ 𝒴.erase Y₀ := Finset.mem_erase.mpr ⟨hYY, hY⟩
      have hYeq : Y = L \ Y₀ := by
        by_contra hne
        have hd := hRdis Y hYR _ hP hne
        obtain ⟨w, hw⟩ := hRne' Y hYR
        exact Finset.disjoint_left.mp hd hw (hRsub Y hYR hw)
      rw [hYeq]
      refine ⟨Finset.mem_singleton_self _, ?_⟩
      exact (ep_flat_leaf ({L \ Y₀} : Finset (Finset W))
        (fun S hS => by rw [Finset.mem_singleton.mp hS]; exact Finset.card_pos.mp (by omega))
        (fun S hS S' hS' hne => absurd ((Finset.mem_singleton.mp hS).trans
          (Finset.mem_singleton.mp hS').symm) hne) _ (Finset.mem_singleton_self _)).1
  · -- two levels: `L \ Y₀` and, strictly inside it, the other members
    have hRss : ∀ R ∈ 𝒴.erase Y₀, R ⊂ L \ Y₀ := fun R hR =>
      Finset.ssubset_iff_subset_ne.mpr ⟨hRsub R hR, fun h' => hP (h' ▸ hR)⟩
    have hPss : L \ Y₀ ⊂ L :=
      Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, fun h' => hrP (by rw [h']; exact hr)⟩
    have hmemS : ∀ S, S ∈ insert (L \ Y₀) (𝒴.erase Y₀) ↔ S = L \ Y₀ ∨ S ∈ 𝒴.erase Y₀ :=
      fun S => Finset.mem_insert
    -- no member lies strictly inside a member of the second level
    have hleaf : ∀ R ∈ 𝒴.erase Y₀, ∀ C ∈ insert (L \ Y₀) (𝒴.erase Y₀), ¬C ⊂ R := by
      intro R hR C hC hCR
      rcases (hmemS C).mp hC with rfl | hC'
      · exact hCR.2 (hRsub R hR)
      · obtain ⟨w, hw⟩ := hRne' C hC'
        have hd := hRdis C hC' R hR (fun h' => hCR.2 (h' ▸ Finset.Subset.refl _))
        exact Finset.disjoint_left.mp hd hw (hCR.1 hw)
    have hchL : epChildren (insert (L \ Y₀) (𝒴.erase Y₀)) L = {L \ Y₀} := by
      ext C
      unfold epChildren
      rw [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hC, hCL, hmax⟩
        rcases (hmemS C).mp hC with h' | h'
        · exact h'
        · exact absurd hPss (hmax _ (Finset.mem_insert_self _ _) (hRss C h'))
      · rintro rfl
        refine ⟨Finset.mem_insert_self _ _, hPss, fun D hD hPD hDL => ?_⟩
        rcases (hmemS D).mp hD with h' | h'
        · exact hPD.2 (h' ▸ Finset.Subset.refl _)
        · exact hPD.2 (hRsub D h')
    have hatL : epAtom (insert (L \ Y₀) (𝒴.erase Y₀)) L = Y₀ := by
      ext w
      rw [mem_epAtom]
      constructor
      · rintro ⟨h1, h2'⟩
        by_contra h'
        exact h2' _ (Finset.mem_insert_self _ _) hPss (Finset.mem_sdiff.mpr ⟨h1, h'⟩)
      · intro hw
        refine ⟨hY₀L hw, fun C hC _ hwC => ?_⟩
        rcases (hmemS C).mp hC with rfl | h'
        · exact (Finset.mem_sdiff.mp hwC).2 hw
        · exact (Finset.mem_sdiff.mp (hRsub C h' hwC)).2 hw
    have hchP : epChildren (insert (L \ Y₀) (𝒴.erase Y₀)) (L \ Y₀) = 𝒴.erase Y₀ := by
      ext C
      unfold epChildren
      rw [Finset.mem_filter]
      constructor
      · rintro ⟨hC, hCP, -⟩
        rcases (hmemS C).mp hC with h' | h'
        · exact absurd (h' ▸ Finset.Subset.refl _) hCP.2
        · exact h'
      · intro hC
        refine ⟨Finset.mem_insert_of_mem hC, hRss C hC, fun D hD hCD hDP => ?_⟩
        rcases (hmemS D).mp hD with h' | h'
        · exact hDP.2 (by rw [h'])
        · exact hleaf D h' C (Finset.mem_insert_of_mem hC) hCD
    have hRleaf : ∀ R ∈ 𝒴.erase Y₀, epChildren (insert (L \ Y₀) (𝒴.erase Y₀)) R = ∅ ∧
        epAtom (insert (L \ Y₀) (𝒴.erase Y₀)) R = R := by
      intro R hR
      constructor
      · unfold epChildren
        rw [Finset.filter_eq_empty_iff]
        intro C hC h'
        exact hleaf R hR C hC h'.1
      · ext w
        rw [mem_epAtom]
        exact ⟨fun h' => h'.1, fun h' => ⟨h', fun C hC hCR => absurd hCR (hleaf R hR C hC)⟩⟩
    -- the atom of `L \ Y₀` is nonempty when there is only one other member
    have hatP : 2 ≤ (epAtom (insert (L \ Y₀) (𝒴.erase Y₀)) (L \ Y₀)).card + (𝒴.erase Y₀).card := by
      by_cases hc : 2 ≤ (𝒴.erase Y₀).card
      · omega
      · have hc1 : (𝒴.erase Y₀).card = 1 := by
          have := Finset.card_pos.mpr hRne; omega
        obtain ⟨R, hR⟩ := Finset.card_eq_one.mp hc1
        have hRm : R ∈ 𝒴.erase Y₀ := by rw [hR]; exact Finset.mem_singleton_self R
        obtain ⟨w, hwP, hwR⟩ := Finset.exists_of_ssubset (hRss R hRm)
        have : w ∈ epAtom (insert (L \ Y₀) (𝒴.erase Y₀)) (L \ Y₀) := by
          rw [mem_epAtom]
          refine ⟨hwP, fun C hC hCP hwC => ?_⟩
          rcases (hmemS C).mp hC with h' | h'
          · exact hCP.2 (h' ▸ Finset.Subset.refl _)
          · rw [hR, Finset.mem_singleton] at h'
            exact hwR (h' ▸ hwC)
        have := Finset.card_pos.mpr ⟨w, this⟩
        omega
    have hcutP : (epCut α β (L \ Y₀)).card = (epCut α β Y₀).card := by
      have : epCut α β (L \ Y₀) = epCut α β Y₀ := by
        ext g; rw [mem_epCut, mem_epCut]
        exact epD_cross_compl α β L Y₀ (L \ Y₀) h (fun w => Finset.mem_sdiff) g
      rw [this]
    have hLnot : L ∉ insert (L \ Y₀) (𝒴.erase Y₀) := by
      intro h'
      rcases (hmemS L).mp h' with h'' | h''
      · exact hPss.2 (h'' ▸ Finset.Subset.refl _)
      · exact hRr L h'' hr
    refine ⟨insert (L \ Y₀) (𝒴.erase Y₀), ⟨?_, ?_, ?_⟩, ?_⟩
    · -- laminar
      intro S hS S' hS'
      rcases (hmemS S).mp hS with rfl | h1 <;> rcases (hmemS S').mp hS' with rfl | h1'
      · exact Or.inl (Finset.Subset.refl _)
      · exact Or.inr (Or.inl (hRsub S' h1'))
      · exact Or.inl (hRsub S h1)
      · by_cases hne : S = S'
        · exact Or.inl (hne ▸ Finset.Subset.refl _)
        · exact Or.inr (Or.inr (hRdis S h1 S' h1' hne))
    · intro S hS
      rcases (hmemS S).mp hS with rfl | h1
      · obtain ⟨R, hR⟩ := hRne
        obtain ⟨w, hw⟩ := hRne' R hR
        exact ⟨Finset.sdiff_subset, ⟨w, hRsub R hR hw⟩, hrP, by rw [hcutP]; exact hY₀cut⟩
      · exact ⟨(hmem S (Finset.mem_of_mem_erase h1)).1, hRne' S h1, hRr S h1,
          (hmem S (Finset.mem_of_mem_erase h1)).2.2⟩
    · intro N hN
      rcases Finset.mem_insert.mp hN with rfl | hN'
      · rw [hchL, hatL, if_pos rfl, Finset.card_singleton]; omega
      · have hNL : ¬(N = L) := fun h' => hLnot (h' ▸ hN')
        rw [if_neg hNL]
        rcases (hmemS N).mp hN' with rfl | h1
        · rw [hchP]; omega
        · obtain ⟨c1, c2⟩ := hRleaf N h1
          rw [c1, c2, Finset.card_empty]
          have := (hmem N (Finset.mem_of_mem_erase h1)).2.1
          omega
    · intro Y hY
      by_cases hYY : Y = Y₀
      · rw [hYY]
        exact Or.inr ⟨hrY₀, hatL.symm, by rw [hchL, Finset.card_singleton]⟩
      · have hYR : Y ∈ 𝒴.erase Y₀ := Finset.mem_erase.mpr ⟨hYY, hY⟩
        exact Or.inl ⟨Finset.mem_insert_of_mem hYR, (hRleaf Y hYR).1⟩

/-- Every member strictly inside a node lies in a child of the node. -/
lemma ep_child_above {W : Type*} [DecidableEq W] (𝒮 : Finset (Finset W)) (N S : Finset W)
    (hS : S ∈ 𝒮) (hSN : S ⊂ N) : ∃ C ∈ epChildren 𝒮 N, S ⊆ C := by
  have hne : (𝒮.filter (fun D => S ⊆ D ∧ D ⊂ N)).Nonempty :=
    ⟨S, Finset.mem_filter.mpr ⟨hS, Finset.Subset.refl _, hSN⟩⟩
  obtain ⟨D, hD, hmax⟩ := Finset.exists_max_image _ Finset.card hne
  rw [Finset.mem_filter] at hD
  refine ⟨D, ?_, hD.2.1⟩
  unfold epChildren
  rw [Finset.mem_filter]
  refine ⟨hD.1, hD.2.2, fun D' hD' hDD' hD'N => ?_⟩
  have := hmax D' (Finset.mem_filter.mpr ⟨hD', hD.2.1.trans hDD'.1, hD'N⟩)
  exact absurd (Finset.card_lt_card hDD') (not_lt.mpr this)

/-- Distinct children of a node of a laminar family are disjoint. -/
lemma ep_children_disjoint {W : Type*} [DecidableEq W] (𝒮 : Finset (Finset W))
    (hlam : EpLaminar 𝒮) (N C D : Finset W) (hC : C ∈ epChildren 𝒮 N)
    (hD : D ∈ epChildren 𝒮 N) (hne : C ≠ D) : Disjoint C D := by
  unfold epChildren at hC hD
  rw [Finset.mem_filter] at hC hD
  rcases hlam C hC.1 D hD.1 with h' | h' | h'
  · exact absurd hD.2.1 (hC.2.2 D hD.1 (Finset.ssubset_iff_subset_ne.mpr ⟨h', hne⟩))
  · exact absurd hC.2.1 (hD.2.2 C hC.1 (Finset.ssubset_iff_subset_ne.mpr ⟨h', hne.symm⟩))
  · exact h'

lemma mem_epChildren {W : Type*} [DecidableEq W] (𝒮 : Finset (Finset W)) (N C : Finset W) :
    C ∈ epChildren 𝒮 N ↔ C ∈ 𝒮 ∧ C ⊂ N ∧ ∀ D ∈ 𝒮, C ⊂ D → ¬D ⊂ N := by
  unfold epChildren
  rw [Finset.mem_filter]

set_option maxHeartbeats 1600000 in
open Classical in
/-- **Inserting a cut into a decomposition.** Let `N` be a node and `Z ⊆ N` a set with a cut of
size two or three, not containing the root vertex, that contains or avoids each child of `N`,
with at least two "items" (atom vertices or children) inside and enough items outside. Then
`Z` is not a member, the family with `Z` added is a decomposition, and it refines every
collection refined by the old one that does not contain the atom of `N`. -/
theorem ep_decomp_insert {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (r : W)
    (𝒮 : Finset (Finset W)) (hdec : EpDecomp α β L r 𝒮) (hr : r ∈ L) (N Z : Finset W)
    (hN : N ∈ insert L 𝒮) (hZN : Z ⊆ N) (hrZ : r ∉ Z)
    (hcut : (epCut α β Z).card = 2 ∨ (epCut α β Z).card = 3)
    (hch : ∀ C ∈ epChildren 𝒮 N, C ⊆ Z ∨ Disjoint C Z)
    (hin : 2 ≤ (epAtom 𝒮 N ∩ Z).card + ((epChildren 𝒮 N).filter (fun C => C ⊆ Z)).card)
    (hout : 2 ≤ (epAtom 𝒮 N \ Z).card + ((epChildren 𝒮 N).filter (fun C => Disjoint C Z)).card +
      (if N = L then 0 else 1)) :
    Z ∉ 𝒮 ∧ EpDecomp α β L r (insert Z 𝒮) ∧
      ∀ 𝒴, EpRefines L r 𝒮 𝒴 → epAtom 𝒮 N ∉ 𝒴 → EpRefines L r (insert Z 𝒮) 𝒴 := by
  obtain ⟨hlam, hmem, hnode⟩ := hdec
  have hNL : N ⊆ L := by
    rcases Finset.mem_insert.mp hN with rfl | h'
    · exact Finset.Subset.refl _
    · exact (hmem N h').1
  have hSne : ∀ S ∈ 𝒮, S.Nonempty := fun S hS => (hmem S hS).2.1
  have hSL : ∀ S ∈ 𝒮, S ⊂ L := fun S hS =>
    Finset.ssubset_iff_subset_ne.mpr ⟨(hmem S hS).1, fun h' => (hmem S hS).2.2.1 (h' ▸ hr)⟩
  have hchS : ∀ C ∈ epChildren 𝒮 N, C ∈ 𝒮 ∧ C ⊂ N := fun C hC =>
    ⟨((mem_epChildren 𝒮 N C).mp hC).1, ((mem_epChildren 𝒮 N C).mp hC).2.1⟩
  -- `Z` is nonempty
  have hZne : Z.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have h1 : (epAtom 𝒮 N ∩ Z).card = 0 := by rw [hemp, Finset.inter_empty, Finset.card_empty]
    have h2 : ((epChildren 𝒮 N).filter (fun C => C ⊆ Z)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro C hC hCZ
      obtain ⟨w, hw⟩ := hSne C (hchS C hC).1
      rw [hemp] at hCZ
      exact absurd (hCZ hw) (Finset.notMem_empty w)
    omega
  -- members strictly inside `N` are inside `Z` or disjoint from it
  have hsubZ : ∀ S ∈ 𝒮, S ⊂ N → S ⊆ Z ∨ Disjoint S Z := by
    intro S hS hSN
    obtain ⟨C, hC, hSC⟩ := ep_child_above 𝒮 N S hS hSN
    rcases hch C hC with h' | h'
    · exact Or.inl (hSC.trans h')
    · exact Or.inr (Finset.disjoint_of_subset_left hSC h')
  have hrel : ∀ S ∈ 𝒮, S ⊂ N ∨ N ⊆ S ∨ Disjoint S N := by
    intro S hS
    rcases Finset.mem_insert.mp hN with rfl | h'
    · exact Or.inl (hSL S hS)
    · rcases hlam S hS N h' with h'' | h'' | h''
      · by_cases he : S = N
        · exact Or.inr (Or.inl (he ▸ Finset.Subset.refl _))
        · exact Or.inl (Finset.ssubset_iff_subset_ne.mpr ⟨h'', he⟩)
      · exact Or.inr (Or.inl h'')
      · exact Or.inr (Or.inr h'')
  -- `Z ≠ N`
  have hZneN : Z ≠ N := by
    intro he
    have h1 : (epAtom 𝒮 N \ Z).card = 0 := by
      rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset, he]
      intro w hw; exact ((mem_epAtom 𝒮 N w).mp hw).1
    have h2 : ((epChildren 𝒮 N).filter (fun C => Disjoint C Z)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro C hC hCZ
      obtain ⟨w, hw⟩ := hSne C (hchS C hC).1
      exact Finset.disjoint_left.mp hCZ hw (he ▸ (hchS C hC).2.1 hw)
    split_ifs at hout <;> omega
  have hZssN : Z ⊂ N := Finset.ssubset_iff_subset_ne.mpr ⟨hZN, hZneN⟩
  -- `Z` is not a member
  have hZnot : Z ∉ 𝒮 := by
    intro hZS
    obtain ⟨C, hC, hZC⟩ := ep_child_above 𝒮 N Z hZS hZssN
    have hCZ : C = Z := by
      rcases hch C hC with h' | h'
      · exact Finset.Subset.antisymm h' hZC
      · obtain ⟨w, hw⟩ := hZne
        exact absurd hw (Finset.disjoint_left.mp h' (hZC hw))
    have h1 : (epAtom 𝒮 N ∩ Z).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro w hw
      rw [Finset.mem_inter, mem_epAtom] at hw
      exact hw.1.2 Z hZS hZssN hw.2
    have h2 : ((epChildren 𝒮 N).filter (fun C => C ⊆ Z)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro D hD D' hD'
      rw [Finset.mem_filter] at hD hD'
      have key : ∀ D ∈ epChildren 𝒮 N, D ⊆ Z → D = C := by
        intro D hD hDZ
        by_contra hne
        obtain ⟨w, hw⟩ := hSne D (hchS D hD).1
        exact Finset.disjoint_left.mp (ep_children_disjoint 𝒮 hlam N D C hD hC hne) hw
          (hCZ ▸ hDZ hw)
      rw [key D hD.1 hD.2, key D' hD'.1 hD'.2]
    omega
  have hZL : Z ⊂ L := lt_of_lt_of_le hZssN hNL
  have hmemS : ∀ S, S ∈ insert Z 𝒮 ↔ S = Z ∨ S ∈ 𝒮 := fun S => Finset.mem_insert
  -- relation of the members to `Z`
  have hrelZ : ∀ S ∈ 𝒮, S ⊂ Z ∨ Z ⊂ S ∨ Disjoint S Z := by
    intro S hS
    rcases hrel S hS with h' | h' | h'
    · rcases hsubZ S hS h' with h'' | h''
      · exact Or.inl (Finset.ssubset_iff_subset_ne.mpr ⟨h'', fun he => hZnot (he ▸ hS)⟩)
      · exact Or.inr (Or.inr h'')
    · exact Or.inr (Or.inl (lt_of_lt_of_le hZssN h'))
    · exact Or.inr (Or.inr (Finset.disjoint_of_subset_right hZN h'))
  -- a node other than `N` that strictly contains `Z` strictly contains `N`
  have habove : ∀ M ∈ insert L 𝒮, M ≠ N → Z ⊂ M → N ⊂ M ∧ N ∈ 𝒮 := by
    intro M hM hMN hZM
    have hNM : N ⊂ M := by
      rcases Finset.mem_insert.mp hM with rfl | hM'
      · exact Finset.ssubset_iff_subset_ne.mpr ⟨hNL, fun h' => hMN h'.symm⟩
      · rcases hrel M hM' with h' | h' | h'
        · rcases hsubZ M hM' h' with h'' | h''
          · exact absurd h'' hZM.2
          · obtain ⟨w, hw⟩ := hZne
            exact absurd hw (Finset.disjoint_left.mp h'' (hZM.1 hw))
        · exact Finset.ssubset_iff_subset_ne.mpr ⟨h', fun he => hMN he.symm⟩
        · obtain ⟨w, hw⟩ := hZne
          exact absurd (hZN hw) (Finset.disjoint_left.mp h' (hZM.1 hw))
    refine ⟨hNM, ?_⟩
    rcases Finset.mem_insert.mp hN with rfl | h'
    · have hML : M ⊆ N := by
        rcases Finset.mem_insert.mp hM with rfl | hM'
        · exact Finset.Subset.refl _
        · exact (hmem M hM').1
      exact absurd hML hNM.2
    · exact h'
  -- atoms and children of the nodes other than `N`
  have hother : ∀ M ∈ insert L 𝒮, M ≠ N →
      epAtom (insert Z 𝒮) M = epAtom 𝒮 M ∧ epChildren (insert Z 𝒮) M = epChildren 𝒮 M := by
    intro M hM hMN
    constructor
    · ext v
      rw [mem_epAtom, mem_epAtom]
      constructor
      · exact fun h' => ⟨h'.1, fun C hC => h'.2 C (Finset.mem_insert_of_mem hC)⟩
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun C hC hCM hvC => ?_⟩
        rcases (hmemS C).mp hC with rfl | hC'
        · obtain ⟨a1, a2⟩ := habove M hM hMN hCM
          exact h2 N a2 a1 (hZN hvC)
        · exact h2 C hC' hCM hvC
    · ext C
      rw [mem_epChildren, mem_epChildren]
      constructor
      · rintro ⟨h1, h2, h3⟩
        rcases (hmemS C).mp h1 with rfl | hC'
        · obtain ⟨a1, a2⟩ := habove M hM hMN h2
          exact absurd a1 (h3 N (Finset.mem_insert_of_mem a2) hZssN)
        · exact ⟨hC', h2, fun D hD => h3 D (Finset.mem_insert_of_mem hD)⟩
      · rintro ⟨h1, h2, h3⟩
        refine ⟨Finset.mem_insert_of_mem h1, h2, fun D hD hCD hDM => ?_⟩
        rcases (hmemS D).mp hD with rfl | hD'
        · obtain ⟨a1, a2⟩ := habove M hM hMN hDM
          exact h3 N a2 (lt_trans hCD hZssN) a1
        · exact h3 D hD' hCD hDM
  -- the node `N`
  have hatomN : epAtom (insert Z 𝒮) N = epAtom 𝒮 N \ Z := by
    ext v
    rw [Finset.mem_sdiff, mem_epAtom, mem_epAtom]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, fun C hC => h2 C (Finset.mem_insert_of_mem hC)⟩,
        h2 Z (Finset.mem_insert_self _ _) hZssN⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, fun C hC hCN hvC => ?_⟩
      rcases (hmemS C).mp hC with rfl | hC'
      · exact h3 hvC
      · exact h2 C hC' hCN hvC
  have hchN : epChildren (insert Z 𝒮) N =
      insert Z ((epChildren 𝒮 N).filter (fun C => Disjoint C Z)) := by
    ext C
    constructor
    · intro hC
      obtain ⟨h1, h2, h3⟩ := (mem_epChildren _ N C).mp hC
      rcases (hmemS C).mp h1 with rfl | hC'
      · exact Finset.mem_insert_self _ _
      · refine Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨(mem_epChildren 𝒮 N C).mpr
          ⟨hC', h2, fun D hD => h3 D (Finset.mem_insert_of_mem hD)⟩, ?_⟩)
        rcases hsubZ C hC' h2 with h' | h'
        · exact absurd hZssN (h3 Z (Finset.mem_insert_self _ _)
            (Finset.ssubset_iff_subset_ne.mpr ⟨h', fun he => hZnot (he ▸ hC')⟩))
        · exact h'
    · intro hC
      rw [mem_epChildren]
      rcases Finset.mem_insert.mp hC with rfl | hC
      · refine ⟨Finset.mem_insert_self _ _, hZssN, fun D hD hCD hDN => ?_⟩
        rcases (hmemS D).mp hD with rfl | hD'
        · exact hCD.2 (Finset.Subset.refl _)
        · rcases hsubZ D hD' hDN with h' | h'
          · exact hCD.2 h'
          · obtain ⟨w, hw⟩ := hZne
            exact Finset.disjoint_left.mp h' (hCD.1 hw) hw
      · rw [Finset.mem_filter, mem_epChildren] at hC
        obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hC
        refine ⟨Finset.mem_insert_of_mem h1, h2, fun D hD hCD hDN => ?_⟩
        rcases (hmemS D).mp hD with rfl | hD'
        · obtain ⟨w, hw⟩ := hSne C h1
          exact Finset.disjoint_left.mp h4 hw (hCD.1 hw)
        · exact h3 D hD' hCD hDN
  -- the node `Z`
  have hatomZ : epAtom (insert Z 𝒮) Z = epAtom 𝒮 N ∩ Z := by
    ext v
    rw [Finset.mem_inter, mem_epAtom, mem_epAtom]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨hZN h1, fun C hC hCN hvC => ?_⟩, h1⟩
      rcases hsubZ C hC hCN with h' | h'
      · exact h2 C (Finset.mem_insert_of_mem hC)
          (Finset.ssubset_iff_subset_ne.mpr ⟨h', fun he => hZnot (he ▸ hC)⟩) hvC
      · exact Finset.disjoint_left.mp h' hvC h1
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h3, fun C hC hCZ hvC => ?_⟩
      rcases (hmemS C).mp hC with rfl | hC'
      · exact hCZ.2 (Finset.Subset.refl _)
      · exact h2 C hC' (lt_trans hCZ hZssN) hvC
  have hchZ : epChildren (insert Z 𝒮) Z = (epChildren 𝒮 N).filter (fun C => C ⊆ Z) := by
    ext C
    rw [mem_epChildren, Finset.mem_filter, mem_epChildren]
    constructor
    · rintro ⟨h1, h2, h3⟩
      rcases (hmemS C).mp h1 with rfl | hC'
      · exact absurd (Finset.Subset.refl _) h2.2
      · refine ⟨⟨hC', lt_trans h2 hZssN, fun D hD hCD hDN => ?_⟩, h2.1⟩
        rcases hsubZ D hD hDN with h' | h'
        · exact h3 D (Finset.mem_insert_of_mem hD) hCD
            (Finset.ssubset_iff_subset_ne.mpr ⟨h', fun he => hZnot (he ▸ hD)⟩)
        · obtain ⟨w, hw⟩ := hSne C hC'
          exact Finset.disjoint_left.mp h' (hCD.1 hw) (h2.1 hw)
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      refine ⟨Finset.mem_insert_of_mem h1, Finset.ssubset_iff_subset_ne.mpr
        ⟨h4, fun he => hZnot (he ▸ h1)⟩, fun D hD hCD hDZ => ?_⟩
      rcases (hmemS D).mp hD with rfl | hD'
      · exact hDZ.2 (Finset.Subset.refl _)
      · exact h3 D hD' hCD (lt_trans hDZ hZssN)
  refine ⟨hZnot, ⟨?_, ?_, ?_⟩, ?_⟩
  · -- laminar
    intro S hS S' hS'
    rcases (hmemS S).mp hS with rfl | h1 <;> rcases (hmemS S').mp hS' with rfl | h1'
    · exact Or.inl (Finset.Subset.refl _)
    · rcases hrelZ S' h1' with h' | h' | h'
      · exact Or.inr (Or.inl h'.1)
      · exact Or.inl h'.1
      · exact Or.inr (Or.inr h'.symm)
    · rcases hrelZ S h1 with h' | h' | h'
      · exact Or.inl h'.1
      · exact Or.inr (Or.inl h'.1)
      · exact Or.inr (Or.inr h')
    · exact hlam S h1 S' h1'
  · intro S hS
    rcases (hmemS S).mp hS with rfl | h1
    · exact ⟨hZL.1, hZne, hrZ, hcut⟩
    · exact hmem S h1
  · intro M hM
    by_cases hMZ : M = Z
    · rw [hMZ, hatomZ, hchZ, if_neg (fun he : Z = L => hZL.2 (by rw [he]))]
      omega
    · by_cases hMN : M = N
      · rw [hMN, hatomN, hchN, Finset.card_insert_of_notMem
          (fun h' => hZnot (hchS Z (Finset.mem_of_mem_filter _ h')).1)]
        split_ifs at hout ⊢ <;> omega
      · have hM' : M ∈ insert L 𝒮 := by
          rcases Finset.mem_insert.mp hM with h' | h'
          · exact Finset.mem_insert.mpr (Or.inl h')
          · rcases (hmemS M).mp h' with h'' | h''
            · exact absurd h'' hMZ
            · exact Finset.mem_insert_of_mem h''
        obtain ⟨a1, a2⟩ := hother M hM' hMN
        rw [a1, a2]
        exact hnode M hM'
  · intro 𝒴 href hA Y hY
    rcases href Y hY with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · left
      have hYN : Y ≠ N := by
        intro he
        apply hA
        have : epAtom 𝒮 N = N := by
          rw [ep_atom_children, ← he, h2, Finset.biUnion_empty, Finset.sdiff_empty]
        rw [this, ← he]; exact hY
      obtain ⟨a1, a2⟩ := hother Y (Finset.mem_insert_of_mem h1) hYN
      exact ⟨Finset.mem_insert_of_mem h1, a2.trans h2⟩
    · right
      have hLN : L ≠ N := by
        intro he
        apply hA
        rw [← he, ← h2]; exact hY
      obtain ⟨a1, a2⟩ := hother L (Finset.mem_insert_self _ _) hLN
      exact ⟨h1, by rw [a1]; exact h2, by rw [a2]; exact h3⟩

open Classical in
/-- The sets contracted to form the hub at a node `N`: the children of `N` and, unless `N` is
the root node, the complement of `N`. -/
noncomputable def epHubFam {W : Type*} (𝒮 : Finset (Finset W)) (L N : Finset W) :
    Finset (Finset W) :=
  epChildren 𝒮 N ∪ (if N = L then ∅ else {L \ N})

open Classical in
lemma mem_epHubFam {W : Type*} (𝒮 : Finset (Finset W)) (L N C : Finset W) :
    C ∈ epHubFam 𝒮 L N ↔ C ∈ epChildren 𝒮 N ∨ (N ≠ L ∧ C = L \ N) := by
  unfold epHubFam
  rw [Finset.mem_union]
  by_cases hNL : N = L
  · rw [if_pos hNL]; simp [hNL]
  · rw [if_neg hNL, Finset.mem_singleton]; tauto

open Classical in
/-- The family contracted at a node consists of pairwise disjoint sets with cuts of size two or
three, and what is left is the atom of the node. -/
theorem ep_hubFam_spec {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (r : W)
    (𝒮 : Finset (Finset W)) (h : EpCubicD α β L) (hr : r ∈ L) (hdec : EpDecomp α β L r 𝒮)
    (N : Finset W) (hN : N ∈ insert L 𝒮) :
    (∀ C ∈ epHubFam 𝒮 L N, C ⊆ L ∧ C.Nonempty ∧ (∀ a ∈ epAtom 𝒮 N, a ∉ C) ∧
      ((epCut α β C).card = 2 ∨ (epCut α β C).card = 3)) ∧
    (∀ C ∈ epHubFam 𝒮 L N, ∀ C' ∈ epHubFam 𝒮 L N, C ≠ C' → Disjoint C C') ∧
    L \ (epHubFam 𝒮 L N).biUnion id = epAtom 𝒮 N := by
  obtain ⟨hlam, hmem, hnode⟩ := hdec
  have hNL : N ⊆ L := by
    rcases Finset.mem_insert.mp hN with rfl | h'
    · exact Finset.Subset.refl _
    · exact (hmem N h').1
  have hNS : N ≠ L → N ∈ 𝒮 := fun hne =>
    (Finset.mem_insert.mp hN).elim (fun h' => absurd h' hne) id
  have hchS : ∀ C ∈ epChildren 𝒮 N, C ∈ 𝒮 ∧ C ⊂ N := fun C hC =>
    ⟨((mem_epChildren 𝒮 N C).mp hC).1, ((mem_epChildren 𝒮 N C).mp hC).2.1⟩
  have hcompl : epCut α β (L \ N) = epCut α β N := by
    ext g; rw [mem_epCut, mem_epCut]
    exact epD_cross_compl α β L N (L \ N) h (fun w => Finset.mem_sdiff) g
  refine ⟨fun C hC => ?_, fun C hC C' hC' hne => ?_, ?_⟩
  · rcases (mem_epHubFam 𝒮 L N C).mp hC with h' | ⟨h1, rfl⟩
    · obtain ⟨a1, a2⟩ := hchS C h'
      obtain ⟨b1, b2, -, b4⟩ := hmem C a1
      exact ⟨b1, b2, fun a ha => ((mem_epAtom 𝒮 N a).mp ha).2 C a1 a2, b4⟩
    · obtain ⟨b1, b2, b3, b4⟩ := hmem N (hNS h1)
      refine ⟨Finset.sdiff_subset, ⟨r, Finset.mem_sdiff.mpr ⟨hr, b3⟩⟩, fun a ha h' => ?_, ?_⟩
      · exact (Finset.mem_sdiff.mp h').2 ((mem_epAtom 𝒮 N a).mp ha).1
      · rw [hcompl]; exact b4
  · rcases (mem_epHubFam 𝒮 L N C).mp hC with h1 | ⟨h1, rfl⟩ <;>
      rcases (mem_epHubFam 𝒮 L N C').mp hC' with h2 | ⟨h2, rfl⟩
    · exact ep_children_disjoint 𝒮 hlam N C C' h1 h2 hne
    · rw [Finset.disjoint_left]; intro w hw hw'
      exact (Finset.mem_sdiff.mp hw').2 ((hchS C h1).2.1 hw)
    · rw [Finset.disjoint_left]; intro w hw hw'
      exact (Finset.mem_sdiff.mp hw).2 ((hchS C' h2).2.1 hw')
    · exact absurd rfl hne
  · ext w
    rw [ep_atom_children, Finset.mem_sdiff, Finset.mem_sdiff, Finset.mem_biUnion,
      Finset.mem_biUnion]
    constructor
    · rintro ⟨h1, h2⟩
      have hwN : w ∈ N := by
        by_contra hwN
        have hne : N ≠ L := fun he => hwN (he ▸ h1)
        exact h2 ⟨L \ N, (mem_epHubFam 𝒮 L N _).mpr (Or.inr ⟨hne, rfl⟩),
          Finset.mem_sdiff.mpr ⟨h1, hwN⟩⟩
      refine ⟨hwN, ?_⟩
      rintro ⟨C, hC, hwC⟩
      exact h2 ⟨C, (mem_epHubFam 𝒮 L N C).mpr (Or.inl hC), hwC⟩
    · rintro ⟨h1, h2⟩
      refine ⟨hNL h1, ?_⟩
      rintro ⟨C, hC, hwC⟩
      rcases (mem_epHubFam 𝒮 L N C).mp hC with h' | ⟨-, rfl⟩
      · exact h2 ⟨C, h', hwC⟩
      · exact (Finset.mem_sdiff.mp hwC).2 h1

set_option maxHeartbeats 1600000 in
open Classical in
/-- **Lemma 15 (arXiv numbering).** In a `𝒴`-maximum decomposition, for a node whose atom is not
a member of `𝒴`, every multigraph that is cubic, bridgeless, connected and whose cuts lift to
the graph in the way hubs do is cyclically 4-edge-connected. -/
theorem ep_max_decomp_cyc4 {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (r : W)
    (𝒮 𝒴 : Finset (Finset W)) (h : EpCubicD α β L) (hr : r ∈ L)
    (hdec : EpDecomp α β L r 𝒮) (href : EpRefines L r 𝒮 𝒴)
    (hmax : ∀ 𝒮', EpDecomp α β L r 𝒮' → EpRefines L r 𝒮' 𝒴 → 𝒮'.card ≤ 𝒮.card)
    (N : Finset W) (hN : N ∈ insert L 𝒮) (hA : epAtom 𝒮 N ∉ 𝒴)
    (α' β' : E → W) (L' : Finset W) (h' : EpCubicD α' β' L') (hb' : EpBridgeless α' β' L')
    (hconn' : EpConnected α' β' L')
    (hlift : ∀ T', T' ⊆ L' → ∃ Z, Z ⊆ L ∧
      (∀ w ∈ L \ (epHubFam 𝒮 L N).biUnion id, w ∈ Z ↔ w ∈ T') ∧
      (∀ C ∈ epHubFam 𝒮 L N, C ⊆ Z ∨ Disjoint C Z) ∧
      (epCut α β Z).card = (epCut α' β' T').card ∧
      T'.card ≤ (T' ∩ (L \ (epHubFam 𝒮 L N).biUnion id)).card +
        ((epHubFam 𝒮 L N).filter (fun D => D ⊆ Z)).card ∧
      (L' \ T').card ≤ ((L \ (epHubFam 𝒮 L N).biUnion id) \ T').card +
        ((epHubFam 𝒮 L N).filter (fun D => Disjoint D Z)).card) :
    EpCyc4 α' β' L' := by
  by_contra h4
  obtain ⟨hfam, -, hAeq⟩ := ep_hubFam_spec α β L r 𝒮 h hr hdec N hN
  rw [hAeq] at hlift
  -- a cut of the hub of size two or three with two vertices on each side
  have hT : ∃ T', T' ⊆ L' ∧ ((epCut α' β' T').card = 2 ∨ (epCut α' β' T').card = 3) ∧
      2 ≤ T'.card ∧ 2 ≤ (L' \ T').card := by
    rcases epD_cut_trichotomy α' β' L' h' hb' hconn' with h4' | ⟨X, e, e', hXL, hXne, hXL', hee', hcut⟩ |
      ⟨X, hXL, h3, hX3, hY3⟩
    · exact absurd h4' h4
    · have hc2 : (epCut α' β' X).card = 2 := by
        have : epCut α' β' X = {e, e'} := by
          ext g; rw [mem_epCut, hcut, Finset.mem_insert, Finset.mem_singleton]
        rw [this, Finset.card_pair hee']
      have hcompl : epCut α' β' (L' \ X) = epCut α' β' X := by
        ext g; rw [mem_epCut, mem_epCut]
        exact epD_cross_compl α' β' L' X (L' \ X) h' (fun w => Finset.mem_sdiff) g
      have hone : ∀ T : Finset W, T ⊆ L' → (epCut α' β' T).card = 2 → T.card ≠ 1 := by
        intro T hTL hT2 hT1
        obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hT1
        have := h'.2 c (hTL (by rw [hc]; exact Finset.mem_singleton_self c))
        rw [hc] at hT2; omega
      have h1 := hone X hXL hc2
      have h2 := hone (L' \ X) Finset.sdiff_subset (by rw [hcompl]; exact hc2)
      have h3 := Finset.card_pos.mpr hXne
      have h5 : 0 < (L' \ X).card := by
        rw [Finset.card_pos, Finset.nonempty_iff_ne_empty, Ne, Finset.sdiff_eq_empty_iff_subset]
        exact fun h'' => hXL' (Finset.Subset.antisymm hXL h'')
      exact ⟨X, hXL, Or.inl hc2, by omega, by omega⟩
    · exact ⟨X, hXL, Or.inr h3, by omega, by omega⟩
  obtain ⟨T', hT'L, hT'cut, hT'2, hT'2'⟩ := hT
  obtain ⟨Z₀, hZ₀L, i1, i2, i3, i4, i5⟩ := hlift T' hT'L
  have hAL : epAtom 𝒮 N ⊆ L := by rw [← hAeq]; exact Finset.sdiff_subset
  -- the lifted cut, in a form symmetric under complementation
  have hQ : ∃ Z, Z ⊆ L ∧ r ∉ Z ∧ (∀ C ∈ epHubFam 𝒮 L N, C ⊆ Z ∨ Disjoint C Z) ∧
      ((epCut α β Z).card = 2 ∨ (epCut α β Z).card = 3) ∧
      2 ≤ (epAtom 𝒮 N ∩ Z).card + ((epHubFam 𝒮 L N).filter (fun D => D ⊆ Z)).card ∧
      2 ≤ (epAtom 𝒮 N \ Z).card + ((epHubFam 𝒮 L N).filter (fun D => Disjoint D Z)).card := by
    have e1 : T' ∩ epAtom 𝒮 N = epAtom 𝒮 N ∩ Z₀ := by
      ext w; rw [Finset.mem_inter, Finset.mem_inter]
      exact ⟨fun hw => ⟨hw.2, (i1 w hw.2).mpr hw.1⟩, fun hw => ⟨(i1 w hw.1).mp hw.2, hw.1⟩⟩
    have e2 : epAtom 𝒮 N \ T' = epAtom 𝒮 N \ Z₀ := by
      ext w; rw [Finset.mem_sdiff, Finset.mem_sdiff]
      exact ⟨fun hw => ⟨hw.1, fun h'' => hw.2 ((i1 w hw.1).mp h'')⟩,
        fun hw => ⟨hw.1, fun h'' => hw.2 ((i1 w hw.1).mpr h'')⟩⟩
    rw [e1] at i4
    rw [e2] at i5
    by_cases hrZ : r ∈ Z₀
    · refine ⟨L \ Z₀, Finset.sdiff_subset, fun h'' => (Finset.mem_sdiff.mp h'').2 hrZ,
        fun C hC => ?_, ?_, ?_, ?_⟩
      · rcases i2 C hC with h'' | h''
        · right; rw [Finset.disjoint_left]; intro w hw hw'
          exact (Finset.mem_sdiff.mp hw').2 (h'' hw)
        · left; intro w hw
          exact Finset.mem_sdiff.mpr ⟨(hfam C hC).1 hw, Finset.disjoint_left.mp h'' hw⟩
      · have : epCut α β (L \ Z₀) = epCut α β Z₀ := by
          ext g; rw [mem_epCut, mem_epCut]
          exact epD_cross_compl α β L Z₀ (L \ Z₀) h (fun w => Finset.mem_sdiff) g
        rw [this, i3]; exact hT'cut
      · have a1 : epAtom 𝒮 N ∩ (L \ Z₀) = epAtom 𝒮 N \ Z₀ := by
          ext w; rw [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_sdiff]
          exact ⟨fun hw => ⟨hw.1, hw.2.2⟩, fun hw => ⟨hw.1, hAL hw.1, hw.2⟩⟩
        have a2 : (epHubFam 𝒮 L N).filter (fun D => Disjoint D Z₀) ⊆
            (epHubFam 𝒮 L N).filter (fun D => D ⊆ L \ Z₀) := by
          intro C hC
          rw [Finset.mem_filter] at hC ⊢
          refine ⟨hC.1, fun w hw => ?_⟩
          exact Finset.mem_sdiff.mpr ⟨(hfam C hC.1).1 hw, Finset.disjoint_left.mp hC.2 hw⟩
        have := Finset.card_le_card a2
        rw [a1]; omega
      · have a1 : epAtom 𝒮 N \ (L \ Z₀) = epAtom 𝒮 N ∩ Z₀ := by
          ext w; rw [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_sdiff]
          constructor
          · rintro ⟨hw1, hw2⟩
            exact ⟨hw1, by by_contra h''; exact hw2 ⟨hAL hw1, h''⟩⟩
          · rintro ⟨hw1, hw2⟩
            exact ⟨hw1, fun h'' => h''.2 hw2⟩
        have a2 : (epHubFam 𝒮 L N).filter (fun D => D ⊆ Z₀) ⊆
            (epHubFam 𝒮 L N).filter (fun D => Disjoint D (L \ Z₀)) := by
          intro C hC
          rw [Finset.mem_filter] at hC ⊢
          refine ⟨hC.1, ?_⟩
          rw [Finset.disjoint_left]; intro w hw hw'
          exact (Finset.mem_sdiff.mp hw').2 (hC.2 hw)
        have := Finset.card_le_card a2
        rw [a1]; omega
    · exact ⟨Z₀, hZ₀L, hrZ, i2, by rw [i3]; exact hT'cut, by omega, by omega⟩
  obtain ⟨Z, hZL, hrZ, j2, j3, j4, j5⟩ := hQ
  have hNS : N ≠ L → N ∈ 𝒮 := fun hne =>
    (Finset.mem_insert.mp hN).elim (fun h'' => absurd h'' hne) id
  have hrN : N ≠ L → r ∉ N := fun hne => (hdec.2.1 N (hNS hne)).2.2.1
  -- the complement of `N` is not inside `Z`, hence disjoint from it
  have hcomplZ : N ≠ L → ¬(L \ N ⊆ Z) := fun hne h'' =>
    hrZ (h'' (Finset.mem_sdiff.mpr ⟨hr, hrN hne⟩))
  have hZN : Z ⊆ N := by
    by_cases hNL : N = L
    · rw [hNL]; exact hZL
    · rcases j2 (L \ N) ((mem_epHubFam 𝒮 L N _).mpr (Or.inr ⟨hNL, rfl⟩)) with h'' | h''
      · exact absurd h'' (hcomplZ hNL)
      · intro w hw
        by_contra hwN
        exact Finset.disjoint_left.mp h'' (Finset.mem_sdiff.mpr ⟨hZL hw, hwN⟩) hw
  have c1 : ((epHubFam 𝒮 L N).filter (fun D => D ⊆ Z)).card ≤
      ((epChildren 𝒮 N).filter (fun C => C ⊆ Z)).card := by
    apply Finset.card_le_card
    intro C hC
    rw [Finset.mem_filter] at hC ⊢
    rcases (mem_epHubFam 𝒮 L N C).mp hC.1 with h'' | ⟨h1, rfl⟩
    · exact ⟨h'', hC.2⟩
    · exact absurd hC.2 (hcomplZ h1)
  have c2 : ((epHubFam 𝒮 L N).filter (fun D => Disjoint D Z)).card ≤
      ((epChildren 𝒮 N).filter (fun C => Disjoint C Z)).card + (if N = L then 0 else 1) := by
    by_cases hNL : N = L
    · rw [if_pos hNL, Nat.add_zero]
      apply Finset.card_le_card
      intro C hC
      rw [Finset.mem_filter] at hC ⊢
      rcases (mem_epHubFam 𝒮 L N C).mp hC.1 with h'' | ⟨h1, -⟩
      · exact ⟨h'', hC.2⟩
      · exact absurd hNL h1
    · rw [if_neg hNL]
      refine (Finset.card_le_card (?_ : _ ⊆ insert (L \ N)
        ((epChildren 𝒮 N).filter (fun C => Disjoint C Z)))).trans (Finset.card_insert_le _ _)
      intro C hC
      rw [Finset.mem_filter] at hC
      rcases (mem_epHubFam 𝒮 L N C).mp hC.1 with h'' | ⟨-, rfl⟩
      · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨h'', hC.2⟩)
      · exact Finset.mem_insert_self _ _
  obtain ⟨k1, k2, k3⟩ := ep_decomp_insert α β L r 𝒮 hdec hr N Z hN hZN hrZ j3
    (fun C hC => j2 C ((mem_epHubFam 𝒮 L N C).mpr (Or.inl hC))) (by omega) (by omega)
  have := hmax _ k2 (k3 𝒴 href hA)
  rw [Finset.card_insert_of_notMem k1] at this
  omega

open Classical in
/-- The edges between two vertex sets. -/
noncomputable def epBtw {W E : Type*} [Fintype E] (α β : E → W) (A B : Finset W) : Finset E :=
  Finset.univ.filter (fun g => (α g ∈ A ∧ β g ∈ B) ∨ (α g ∈ B ∧ β g ∈ A))

lemma mem_epBtw {W E : Type*} [Fintype E] (α β : E → W) (A B : Finset W) (g : E) :
    g ∈ epBtw α β A B ↔ (α g ∈ A ∧ β g ∈ B) ∨ (α g ∈ B ∧ β g ∈ A) := by
  classical
  simp [epBtw]

/-- **Cut of a disjoint union**: `d(A ∪ B) + 2 e(A, B) = d(A) + d(B)`. -/
theorem ep_cut_union {W E : Type*} [Fintype E] [DecidableEq W] (α β : E → W) (A B : Finset W)
    (hAB : Disjoint A B) :
    (epCut α β (A ∪ B)).card + 2 * (epBtw α β A B).card =
      (epCut α β A).card + (epCut α β B).card := by
  classical
  have hd : ∀ w, ¬(w ∈ A ∧ w ∈ B) := fun w hw => Finset.disjoint_left.mp hAB hw.1 hw.2
  unfold epCut epBtw
  simp only [Finset.card_filter]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun g _ => ?_
  have h1 := hd (α g)
  have h2 := hd (β g)
  unfold epCross
  simp only [Finset.mem_union]
  by_cases p : α g ∈ A <;> by_cases q : β g ∈ A <;> by_cases r : α g ∈ B <;>
    by_cases s : β g ∈ B <;> simp [p, q, r, s] at h1 h2 ⊢

lemma ep_btw_le_cut {W E : Type*} [Fintype E] (α β : E → W) (A B : Finset W)
    (hAB : Disjoint A B) : (epBtw α β A B).card ≤ (epCut α β A).card := by
  apply Finset.card_le_card
  intro g hg
  rw [mem_epBtw] at hg
  rw [mem_epCut]
  unfold epCross
  rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, fun h' => Finset.disjoint_left.mp hAB h' h2⟩
  · exact Or.inr ⟨fun h' => Finset.disjoint_left.mp hAB h' h1, h2⟩

lemma ep_btw_mono {W E : Type*} [Fintype E] (α β : E → W) (A A' B : Finset W)
    (hA : A ⊆ A') : (epBtw α β A B).card ≤ (epBtw α β A' B).card := by
  apply Finset.card_le_card
  intro g hg
  rw [mem_epBtw] at hg ⊢
  rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨hA h1, h2⟩
  · exact Or.inr ⟨h1, hA h2⟩

lemma ep_btw_comm {W E : Type*} [Fintype E] (α β : E → W) (A B : Finset W) :
    epBtw α β A B = epBtw α β B A := by
  ext g
  rw [mem_epBtw, mem_epBtw]
  exact or_comm

lemma ep_btw_add {W E : Type*} [Fintype E] [DecidableEq W] (α β : E → W) (A B C : Finset W)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) :
    (epBtw α β A B).card + (epBtw α β A C).card ≤ (epBtw α β A (B ∪ C)).card := by
  classical
  have hdis : Disjoint (epBtw α β A B) (epBtw α β A C) := by
    rw [Finset.disjoint_left]
    intro g hg hg'
    rw [mem_epBtw] at hg hg'
    rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hg' with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact Finset.disjoint_left.mp hBC h2 h4
    · exact Finset.disjoint_left.mp hAC h1 h3
    · exact Finset.disjoint_left.mp hAB h3 h1
    · exact Finset.disjoint_left.mp hBC h1 h3
  rw [← Finset.card_union_of_disjoint hdis]
  apply Finset.card_le_card
  intro g hg
  rw [Finset.mem_union, mem_epBtw, mem_epBtw] at hg
  rw [mem_epBtw]
  simp only [Finset.mem_union]
  tauto

/-- In a bridgeless connected multigraph a proper nonempty set has a cut of size at least two. -/
lemma ep_cut_ge_two {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (hb : EpBridgeless α β L) (hconn : EpConnected α β L) (X : Finset W) (hXL : X ⊆ L)
    (hne : X.Nonempty) (hXne : X ≠ L) : 2 ≤ (epCut α β X).card := by
  have h1 := hconn X hXL hne hXne
  have h2 := hb X hXL
  have h3 : (epCut α β X).card ≠ 0 := fun h' => h1 (Finset.card_eq_zero.mp h')
  omega

/-- The pool of small twigs: sets with a cut of size two and between four and eight vertices,
and sets with a cut of size three and exactly five vertices. -/
def EpPool {W E : Type*} [Fintype E] (α β : E → W) (Y : Finset W) : Prop :=
  ((epCut α β Y).card = 2 ∧ 4 ≤ Y.card ∧ Y.card ≤ 8) ∨ ((epCut α β Y).card = 3 ∧ Y.card = 5)

/-- A family of pairwise disjoint sets from the pool. -/
def EpTwigFam {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (𝒴 : Finset (Finset W)) : Prop :=
  (∀ Y ∈ 𝒴, Y ⊆ L ∧ EpPool α β Y) ∧ ∀ Y ∈ 𝒴, ∀ Y' ∈ 𝒴, Y ≠ Y' → Disjoint Y Y'

open Classical in
/-- There is a family of pairwise disjoint pool sets covering the largest number of vertices. -/
theorem ep_twigFam_exists_max {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) :
    ∃ 𝒴, EpTwigFam α β L 𝒴 ∧
      ∀ 𝒴', EpTwigFam α β L 𝒴' → (𝒴'.biUnion id).card ≤ (𝒴.biUnion id).card := by
  have hne : (L.powerset.powerset.filter (fun 𝒴 => EpTwigFam α β L 𝒴)).Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨by simp, ?_⟩⟩
    exact ⟨fun Y hY => absurd hY (Finset.notMem_empty Y),
      fun Y hY => absurd hY (Finset.notMem_empty Y)⟩
  obtain ⟨𝒴, h𝒴, hmax⟩ := Finset.exists_max_image _ (fun 𝒴 => (𝒴.biUnion id).card) hne
  rw [Finset.mem_filter] at h𝒴
  refine ⟨𝒴, h𝒴.2, fun 𝒴' h' => hmax 𝒴' (Finset.mem_filter.mpr ⟨?_, h'⟩)⟩
  rw [Finset.mem_powerset]
  intro Y hY
  rw [Finset.mem_powerset]
  exact (h'.1 Y hY).1

open Classical in
/-- A pool set with two edges to a disjoint triangle-like set absorbs it. -/
lemma ep_pool_absorb {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (hb : EpBridgeless α β L) (hconn : EpConnected α β L) (hbig : 12 ≤ L.card)
    (Y T : Finset W) (hYL : Y ⊆ L) (hY : EpPool α β Y) (hTL : T ⊆ L) (hT3 : T.card = 3)
    (hTcut : (epCut α β T).card = 3) (hYT : Disjoint Y T) (he : 2 ≤ (epBtw α β Y T).card) :
    EpPool α β (Y ∪ T) := by
  have hcu := ep_cut_union α β Y T hYT
  have hcard : (Y ∪ T).card = Y.card + 3 := by rw [Finset.card_union_of_disjoint hYT, hT3]
  have hYle : Y.card ≤ 8 := by rcases hY with h' | h' <;> omega
  have hne : (Y ∪ T).Nonempty := Finset.card_pos.mp (by omega)
  have hneL : Y ∪ T ≠ L := fun h' => by rw [h'] at hcard; omega
  have h2 := ep_cut_ge_two α β L hb hconn (Y ∪ T) (Finset.union_subset hYL hTL) hne hneL
  rcases hY with ⟨a1, a2, a3⟩ | ⟨a1, a2⟩
  · omega
  · exact Or.inl ⟨by omega, by omega, by omega⟩

open Classical in
/-- A vertex of a pool set with two edges leaving the set can be removed from it. -/
lemma ep_pool_strip {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (h : EpCubicD α β L) (hb : EpBridgeless α β L) (hconn : EpConnected α β L)
    (Y R : Finset W) (a : W) (hYL : Y ⊆ L) (hY : EpPool α β Y) (ha : a ∈ Y)
    (hYR : Disjoint Y R) (he : 2 ≤ (epBtw α β {a} R).card) : EpPool α β (Y \ {a}) := by
  have hd1 : Disjoint (Y \ {a}) ({a} : Finset W) := Finset.sdiff_disjoint
  have hYeq : Y \ {a} ∪ {a} = Y := Finset.sdiff_union_of_subset (Finset.singleton_subset_iff.mpr ha)
  have hcu := ep_cut_union α β (Y \ {a}) {a} hd1
  rw [hYeq, h.2 a (hYL ha)] at hcu
  have hdR : Disjoint ({a} : Finset W) R :=
    Finset.disjoint_of_subset_left (Finset.singleton_subset_iff.mpr ha) hYR
  have hdY' : Disjoint ({a} : Finset W) (Y \ {a}) := hd1.symm
  have hd3 : Disjoint (Y \ {a}) R := Finset.disjoint_of_subset_left Finset.sdiff_subset hYR
  have hadd := ep_btw_add α β {a} (Y \ {a}) R hdY' hdR hd3
  have hle := ep_btw_le_cut α β {a} (Y \ {a} ∪ R) (Finset.disjoint_union_right.mpr ⟨hdY', hdR⟩)
  rw [h.2 a (hYL ha)] at hle
  rw [ep_btw_comm α β (Y \ {a}) {a}] at hcu
  have hcard : (Y \ {a}).card + 1 = Y.card := by
    rw [← hYeq, Finset.card_union_of_disjoint hd1, Finset.card_singleton]
    congr 1
    rw [hYeq]
  have hY2 : 2 ≤ Y.card := by rcases hY with h' | h' <;> omega
  have hne : (Y \ {a}).Nonempty := Finset.card_pos.mp (by omega)
  have hneL : Y \ {a} ≠ L := fun h' => by
    have : a ∈ Y \ {a} := by rw [h']; exact hYL ha
    exact (Finset.mem_sdiff.mp this).2 (Finset.mem_singleton_self a)
  have h2 := ep_cut_ge_two α β L hb hconn (Y \ {a}) (Finset.sdiff_subset.trans hYL) hne hneL
  rcases hY with ⟨a1, a2, a3⟩ | ⟨a1, a2⟩
  · omega
  · exact Or.inl ⟨by omega, by omega, by omega⟩

open Classical in
/-- A family covering strictly more vertices contradicts maximality. -/
lemma ep_twigFam_improve {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (𝒴 𝒴' : Finset (Finset W))
    (hmax : ∀ 𝒴', EpTwigFam α β L 𝒴' → (𝒴'.biUnion id).card ≤ (𝒴.biUnion id).card)
    (h' : EpTwigFam α β L 𝒴') (T : Finset W) (hT : T.Nonempty)
    (hTU : Disjoint T (𝒴.biUnion id)) (hsub : 𝒴.biUnion id ∪ T ⊆ 𝒴'.biUnion id) : False := by
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hTU.symm] at h1
  have h2 := hmax 𝒴' h'
  have h3 := Finset.card_pos.mpr hT
  omega

open Classical in
/-- In a family of maximum coverage no member has two edges to a triangle-like set disjoint
from the family. -/
lemma ep_twigFam_absorb_false {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (hb : EpBridgeless α β L) (hconn : EpConnected α β L) (hbig : 12 ≤ L.card)
    (𝒴 : Finset (Finset W)) (hfam : EpTwigFam α β L 𝒴)
    (hmax : ∀ 𝒴', EpTwigFam α β L 𝒴' → (𝒴'.biUnion id).card ≤ (𝒴.biUnion id).card)
    (T : Finset W) (hTL : T ⊆ L) (hT3 : T.card = 3) (hTcut : (epCut α β T).card = 3)
    (hTU : Disjoint T (𝒴.biUnion id)) (Y : Finset W) (hY : Y ∈ 𝒴)
    (he : 2 ≤ (epBtw α β Y T).card) : False := by
  have hTY : ∀ Y' ∈ 𝒴, Disjoint Y' T := fun Y' hY' =>
    (Finset.disjoint_of_subset_right (Finset.subset_biUnion_of_mem id hY') hTU).symm
  have hpool := ep_pool_absorb α β L hb hconn hbig Y T (hfam.1 Y hY).1 (hfam.1 Y hY).2 hTL hT3
    hTcut (hTY Y hY) he
  have hmemS : ∀ S, S ∈ insert (Y ∪ T) (𝒴.erase Y) ↔ S = Y ∪ T ∨ (S ≠ Y ∧ S ∈ 𝒴) := by
    intro S; rw [Finset.mem_insert, Finset.mem_erase]
  have hd : ∀ B, B ≠ Y → B ∈ 𝒴 → Disjoint (Y ∪ T) B := fun B hBY hB =>
    Finset.disjoint_union_left.mpr ⟨hfam.2 Y hY B hB (Ne.symm hBY), (hTY B hB).symm⟩
  refine ep_twigFam_improve α β L 𝒴 (insert (Y ∪ T) (𝒴.erase Y)) hmax ⟨?_, ?_⟩ T
    (Finset.card_pos.mp (by omega)) hTU ?_
  · intro S hS
    rcases (hmemS S).mp hS with rfl | ⟨-, h2⟩
    · exact ⟨Finset.union_subset (hfam.1 Y hY).1 hTL, hpool⟩
    · exact hfam.1 S h2
  · intro A hA B hB hAB
    rcases (hmemS A).mp hA with rfl | ⟨a1, a2⟩ <;> rcases (hmemS B).mp hB with rfl | ⟨b1, b2⟩
    · exact absurd rfl hAB
    · exact hd B b1 b2
    · exact (hd A a1 a2).symm
    · exact hfam.2 A a2 B b2 hAB
  · intro w hw
    rw [Finset.mem_biUnion]
    rcases Finset.mem_union.mp hw with hw | hw
    · obtain ⟨Y₀, hY₀, hwY₀⟩ := Finset.mem_biUnion.mp hw
      by_cases hYY : Y₀ = Y
      · exact ⟨Y ∪ T, Finset.mem_insert_self _ _, Finset.mem_union_left _ (hYY ▸ hwY₀)⟩
      · exact ⟨Y₀, (hmemS Y₀).mpr (Or.inr ⟨hYY, hY₀⟩), hwY₀⟩
    · exact ⟨Y ∪ T, Finset.mem_insert_self _ _, Finset.mem_union_right _ hw⟩

open Classical in
/-- **Diamonds are met.** A triangle-like set `T` with a vertex outside having two edges into
`T` meets a member of a family of maximum coverage. -/
theorem ep_twigFam_meets_diamond {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (h : EpCubicD α β L) (hb : EpBridgeless α β L) (hconn : EpConnected α β L)
    (hbig : 12 ≤ L.card) (𝒴 : Finset (Finset W)) (hfam : EpTwigFam α β L 𝒴)
    (hmax : ∀ 𝒴', EpTwigFam α β L 𝒴' → (𝒴'.biUnion id).card ≤ (𝒴.biUnion id).card)
    (T : Finset W) (hTL : T ⊆ L) (hT3 : T.card = 3) (hTcut : (epCut α β T).card = 3)
    (a : W) (haL : a ∈ L) (haT : a ∉ T) (he : 2 ≤ (epBtw α β {a} T).card) :
    ¬Disjoint T (𝒴.biUnion id) := by
  intro hTU
  by_cases haU : a ∈ 𝒴.biUnion id
  · obtain ⟨Y, hY, haY⟩ := Finset.mem_biUnion.mp haU
    exact ep_twigFam_absorb_false α β L hb hconn hbig 𝒴 hfam hmax T hTL hT3 hTcut hTU Y hY
      (he.trans (ep_btw_mono α β {a} Y T (Finset.singleton_subset_iff.mpr haY)))
  · have hdT : Disjoint T ({a} : Finset W) := Finset.disjoint_singleton_right.mpr haT
    have hcu := ep_cut_union α β T {a} hdT
    rw [hTcut, h.2 a haL, ep_btw_comm α β T {a}] at hcu
    have hcard : (T ∪ {a}).card = 4 := by
      rw [Finset.card_union_of_disjoint hdT, hT3, Finset.card_singleton]
    have hSL : T ∪ {a} ⊆ L := Finset.union_subset hTL (Finset.singleton_subset_iff.mpr haL)
    have h2 := ep_cut_ge_two α β L hb hconn (T ∪ {a}) hSL (Finset.card_pos.mp (by omega))
      (fun h' => by rw [h'] at hcard; omega)
    have hpool : EpPool α β (T ∪ {a}) := Or.inl ⟨by omega, by omega, by omega⟩
    have hd : ∀ B ∈ 𝒴, Disjoint (T ∪ {a}) B := fun B hB =>
      Finset.disjoint_union_left.mpr
        ⟨Finset.disjoint_of_subset_right (Finset.subset_biUnion_of_mem id hB) hTU,
          Finset.disjoint_singleton_left.mpr
            (fun h' => haU (Finset.mem_biUnion.mpr ⟨B, hB, h'⟩))⟩
    refine ep_twigFam_improve α β L 𝒴 (insert (T ∪ {a}) 𝒴) hmax ⟨?_, ?_⟩ T
      (Finset.card_pos.mp (by omega)) hTU ?_
    · intro S hS
      rcases Finset.mem_insert.mp hS with rfl | h2
      · exact ⟨hSL, hpool⟩
      · exact hfam.1 S h2
    · intro A hA B hB hAB
      rcases Finset.mem_insert.mp hA with rfl | a2 <;> rcases Finset.mem_insert.mp hB with rfl | b2
      · exact absurd rfl hAB
      · exact hd B b2
      · exact (hd A a2).symm
      · exact hfam.2 A a2 B b2 hAB
    · intro w hw
      rw [Finset.mem_biUnion]
      rcases Finset.mem_union.mp hw with hw | hw
      · obtain ⟨Y₀, hY₀, hwY₀⟩ := Finset.mem_biUnion.mp hw
        exact ⟨Y₀, Finset.mem_insert_of_mem hY₀, hwY₀⟩
      · exact ⟨T ∪ {a}, Finset.mem_insert_self _ _, Finset.mem_union_left _ hw⟩

set_option maxHeartbeats 1600000 in
open Classical in
/-- **Houses are met.** A triangle-like set `T` with two adjacent vertices outside, each joined
to `T`, meets a member of a family of maximum coverage. -/
theorem ep_twigFam_meets_house {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (h : EpCubicD α β L) (hb : EpBridgeless α β L) (hconn : EpConnected α β L)
    (hbig : 12 ≤ L.card) (𝒴 : Finset (Finset W)) (hfam : EpTwigFam α β L 𝒴)
    (hmax : ∀ 𝒴', EpTwigFam α β L 𝒴' → (𝒴'.biUnion id).card ≤ (𝒴.biUnion id).card)
    (T : Finset W) (hTL : T ⊆ L) (hT3 : T.card = 3) (hTcut : (epCut α β T).card = 3)
    (a b : W) (haL : a ∈ L) (hbL : b ∈ L) (haT : a ∉ T) (hbT : b ∉ T) (hab : a ≠ b)
    (heab : 1 ≤ (epBtw α β {a} {b}).card) (hea : 1 ≤ (epBtw α β {a} T).card)
    (heb : 1 ≤ (epBtw α β {b} T).card) : ¬Disjoint T (𝒴.biUnion id) := by
  intro hTU
  have hdab : Disjoint ({a} : Finset W) {b} := Finset.disjoint_singleton.mpr hab
  have hdaT : Disjoint ({a} : Finset W) T := Finset.disjoint_singleton_left.mpr haT
  have hdbT : Disjoint ({b} : Finset W) T := Finset.disjoint_singleton_left.mpr hbT
  have hTY : ∀ Y' ∈ 𝒴, Disjoint Y' T := fun Y' hY' =>
    (Finset.disjoint_of_subset_right (Finset.subset_biUnion_of_mem id hY') hTU).symm
  -- edges between `T` and `{a, b}`
  have hadd : 2 ≤ (epBtw α β T ({a} ∪ {b})).card := by
    have := ep_btw_add α β T {a} {b} hdaT.symm hdbT.symm hdab
    rw [ep_btw_comm α β T {a}, ep_btw_comm α β T {b}] at this
    omega
  by_cases hboth : ∃ Y ∈ 𝒴, a ∈ Y ∧ b ∈ Y
  · obtain ⟨Y, hY, haY, hbY⟩ := hboth
    refine ep_twigFam_absorb_false α β L hb hconn hbig 𝒴 hfam hmax T hTL hT3 hTcut hTU Y hY ?_
    have hsub : ({a} ∪ {b} : Finset W) ⊆ Y :=
      Finset.union_subset (Finset.singleton_subset_iff.mpr haY)
        (Finset.singleton_subset_iff.mpr hbY)
    have := ep_btw_mono α β ({a} ∪ {b}) Y T hsub
    rw [ep_btw_comm α β T ({a} ∪ {b})] at hadd
    omega
  · -- the house `T ∪ {a, b}`
    have hdT : Disjoint T ({a} ∪ {b} : Finset W) :=
      Finset.disjoint_union_right.mpr ⟨hdaT.symm, hdbT.symm⟩
    have hcu := ep_cut_union α β T ({a} ∪ {b}) hdT
    have hcu2 := ep_cut_union α β {a} {b} hdab
    rw [h.2 a haL, h.2 b hbL] at hcu2
    rw [hTcut] at hcu
    have hcard : (T ∪ ({a} ∪ {b})).card = 5 := by
      rw [Finset.card_union_of_disjoint hdT, hT3, Finset.card_union_of_disjoint hdab,
        Finset.card_singleton, Finset.card_singleton]
    have hSL : T ∪ ({a} ∪ {b}) ⊆ L := Finset.union_subset hTL
      (Finset.union_subset (Finset.singleton_subset_iff.mpr haL)
        (Finset.singleton_subset_iff.mpr hbL))
    have h2 := ep_cut_ge_two α β L hb hconn _ hSL (Finset.card_pos.mp (by omega))
      (fun h' => by rw [h'] at hcard; omega)
    have hpool : EpPool α β (T ∪ ({a} ∪ {b})) := by
      by_cases hc : (epCut α β (T ∪ ({a} ∪ {b}))).card = 2
      · exact Or.inl ⟨hc, by omega, by omega⟩
      · exact Or.inr ⟨by omega, hcard⟩
    -- the stripped members are in the pool
    have hstrip : ∀ Y ∈ 𝒴, Y \ ({a} ∪ {b}) ⊆ L ∧ EpPool α β (Y \ ({a} ∪ {b})) := by
      intro Y hY
      refine ⟨Finset.sdiff_subset.trans (hfam.1 Y hY).1, ?_⟩
      by_cases haY : a ∈ Y
      · have hbY : b ∉ Y := fun h' => hboth ⟨Y, hY, haY, h'⟩
        have heq : Y \ ({a} ∪ {b}) = Y \ {a} := by
          ext w
          simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton]
          constructor
          · rintro ⟨h1, h2⟩; exact ⟨h1, fun h' => h2 (Or.inl h')⟩
          · rintro ⟨h1, h2⟩
            exact ⟨h1, fun h' => h'.elim h2 (fun h'' => hbY (h'' ▸ h1))⟩
        rw [heq]
        refine ep_pool_strip α β L h hb hconn Y (T ∪ {b}) a (hfam.1 Y hY).1 (hfam.1 Y hY).2 haY
          (Finset.disjoint_union_right.mpr ⟨hTY Y hY, Finset.disjoint_singleton_right.mpr hbY⟩) ?_
        have := ep_btw_add α β {a} T {b} hdaT hdab hdbT.symm
        omega
      · by_cases hbY : b ∈ Y
        · have heq : Y \ ({a} ∪ {b}) = Y \ {b} := by
            ext w
            simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton]
            constructor
            · rintro ⟨h1, h2⟩; exact ⟨h1, fun h' => h2 (Or.inr h')⟩
            · rintro ⟨h1, h2⟩
              exact ⟨h1, fun h' => h'.elim (fun h'' => haY (h'' ▸ h1)) h2⟩
          rw [heq]
          refine ep_pool_strip α β L h hb hconn Y (T ∪ {a}) b (hfam.1 Y hY).1 (hfam.1 Y hY).2 hbY
            (Finset.disjoint_union_right.mpr ⟨hTY Y hY, Finset.disjoint_singleton_right.mpr haY⟩)
            ?_
          have := ep_btw_add α β {b} T {a} hdbT hdab.symm hdaT.symm
          rw [ep_btw_comm α β {b} {a}] at this
          omega
        · have heq : Y \ ({a} ∪ {b}) = Y := by
            ext w
            simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton]
            constructor
            · rintro ⟨h1, -⟩; exact h1
            · intro h1
              exact ⟨h1, fun h' => h'.elim (fun h'' => haY (h'' ▸ h1)) (fun h'' => hbY (h'' ▸ h1))⟩
          rw [heq]; exact (hfam.1 Y hY).2
    have hmemS : ∀ S, S ∈ insert (T ∪ ({a} ∪ {b})) (𝒴.image (fun Y => Y \ ({a} ∪ {b}))) ↔
        S = T ∪ ({a} ∪ {b}) ∨ ∃ Y ∈ 𝒴, Y \ ({a} ∪ {b}) = S := by
      intro S; rw [Finset.mem_insert, Finset.mem_image]
    have hd : ∀ Y ∈ 𝒴, Disjoint (T ∪ ({a} ∪ {b})) (Y \ ({a} ∪ {b})) := fun Y hY =>
      Finset.disjoint_union_left.mpr
        ⟨(Finset.disjoint_of_subset_left Finset.sdiff_subset (hTY Y hY)).symm,
          Finset.sdiff_disjoint.symm⟩
    refine ep_twigFam_improve α β L 𝒴
      (insert (T ∪ ({a} ∪ {b})) (𝒴.image (fun Y => Y \ ({a} ∪ {b})))) hmax ⟨?_, ?_⟩ T
      (Finset.card_pos.mp (by omega)) hTU ?_
    · intro S hS
      rcases (hmemS S).mp hS with rfl | ⟨Y, hY, rfl⟩
      · exact ⟨hSL, hpool⟩
      · exact hstrip Y hY
    · intro A hA B hB hAB
      rcases (hmemS A).mp hA with rfl | ⟨Y₁, hY₁, rfl⟩ <;>
        rcases (hmemS B).mp hB with rfl | ⟨Y₂, hY₂, rfl⟩
      · exact absurd rfl hAB
      · exact hd Y₂ hY₂
      · exact (hd Y₁ hY₁).symm
      · have hne : Y₁ ≠ Y₂ := fun h' => hAB (by rw [h'])
        exact Finset.disjoint_of_subset_left Finset.sdiff_subset
          (Finset.disjoint_of_subset_right Finset.sdiff_subset (hfam.2 Y₁ hY₁ Y₂ hY₂ hne))
    · intro w hw
      rw [Finset.mem_biUnion]
      rcases Finset.mem_union.mp hw with hw | hw
      · obtain ⟨Y₀, hY₀, hwY₀⟩ := Finset.mem_biUnion.mp hw
        by_cases hwab : w ∈ ({a} ∪ {b} : Finset W)
        · exact ⟨_, Finset.mem_insert_self _ _, Finset.mem_union_right _ hwab⟩
        · exact ⟨Y₀ \ ({a} ∪ {b}), (hmemS _).mpr (Or.inr ⟨Y₀, hY₀, rfl⟩),
            Finset.mem_sdiff.mpr ⟨hwY₀, hwab⟩⟩
      · exact ⟨_, Finset.mem_insert_self _ _, Finset.mem_union_left _ hw⟩

lemma EpPool.facts {W E : Type*} [Fintype E] {α β : E → W} {Y : Finset W}
    (h : EpPool α β Y) : 4 ≤ Y.card ∧ Y.card ≤ 8 ∧
      ((epCut α β Y).card = 2 ∨ (epCut α β Y).card = 3) := by
  rcases h with ⟨a1, a2, a3⟩ | ⟨a1, a2⟩
  · exact ⟨a2, a3, Or.inl a1⟩
  · exact ⟨by omega, by omega, Or.inr a1⟩

open Classical in
/-- **Corollary 16, second part.** For a multigraph on at least twelve vertices that is not
cyclically 4-edge-connected and a family `𝒴` of pairwise disjoint pool sets there is a
`𝒴`-maximum decomposition. -/
theorem ep_twig_decomp_exists {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (r : W)
    (h : EpCubicD α β L) (hb : EpBridgeless α β L) (hconn : EpConnected α β L) (hr : r ∈ L)
    (h4 : ¬EpCyc4 α β L) (hbig : 12 ≤ L.card) (𝒴 : Finset (Finset W))
    (hfam : EpTwigFam α β L 𝒴) :
    ∃ 𝒮, EpDecomp α β L r 𝒮 ∧ EpRefines L r 𝒮 𝒴 ∧
      ∀ 𝒮', EpDecomp α β L r 𝒮' → EpRefines L r 𝒮' 𝒴 → 𝒮'.card ≤ 𝒮.card := by
  have hex : ∃ 𝒮₀, EpDecomp α β L r 𝒮₀ ∧ EpRefines L r 𝒮₀ 𝒴 := by
    by_cases h0 : 𝒴.card = 0
    · rw [Finset.card_eq_zero] at h0
      rw [h0]
      exact ep_decomp_exists_empty α β L r h hb hconn hr h4
    · by_cases h1 : 𝒴.card = 1
      · obtain ⟨Y, hY⟩ := Finset.card_eq_one.mp h1
        have hYm : Y ∈ 𝒴 := by rw [hY]; exact Finset.mem_singleton_self Y
        obtain ⟨a1, a2, a3⟩ := (hfam.1 Y hYm).2.facts
        have hYL := (hfam.1 Y hYm).1
        rw [hY]
        refine ep_decomp_exists_single α β L r h hr Y hYL (by omega) ?_ a3
        rw [Finset.card_sdiff_of_subset hYL]; omega
      · have h2 : 2 ≤ 𝒴.card := by omega
        by_cases hroot : ∃ Y₀ ∈ 𝒴, r ∈ Y₀
        · obtain ⟨Y₀, hY₀, hrY₀⟩ := hroot
          exact ep_decomp_exists_rooted α β L r h hr 𝒴 Y₀ hY₀ hrY₀ h2
            (fun Y hY => ⟨(hfam.1 Y hY).1, by have := (hfam.1 Y hY).2.facts; omega,
              (hfam.1 Y hY).2.facts.2.2⟩) hfam.2
        · exact ⟨𝒴, ep_decomp_exists_flat α β L r hr 𝒴 h2
            (fun Y hY => ⟨(hfam.1 Y hY).1, by have := (hfam.1 Y hY).2.facts; omega,
              fun h' => hroot ⟨Y, hY, h'⟩, (hfam.1 Y hY).2.facts.2.2⟩) hfam.2⟩
  obtain ⟨𝒮₀, h1, h2⟩ := hex
  exact ep_exists_max_decomp α β L r 𝒴 𝒮₀ h1 h2

/-- An edge crossing exactly the singletons `{x}` and `{y}` joins `x` and `y`. -/
lemma ep_edge_btw {W E : Type*} [Fintype E] (α β : E → W) (x y : W) (e : E) (hxy : x ≠ y)
    (he : ∀ w, epCross α β {w} e ↔ w = x ∨ w = y) : e ∈ epBtw α β {x} {y} := by
  have hx := (he x).mpr (Or.inl rfl)
  have hy := (he y).mpr (Or.inr rfl)
  rw [epCross_singleton] at hx hy
  rw [mem_epBtw]
  simp only [Finset.mem_singleton]
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hy with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · exact absurd (h1.symm.trans h3) hxy
  · exact Or.inl ⟨h1, h4⟩
  · exact Or.inr ⟨h3, h2⟩
  · exact absurd (h2.symm.trans h4) hxy

open Classical in
/-- A triangle of a cubic bridgeless connected multigraph with at least five vertices has
three vertices and a cut of size three. -/
theorem ep_triangle_cut {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (h : EpCubicD α β L) (hb : EpBridgeless α β L) (hconn : EpConnected α β L)
    (hbig : 5 ≤ L.card) (x y z : W) (exy eyz ezx : E)
    (ht : EpTriangle α β L x y z exy eyz ezx) :
    ({x, y, z} : Finset W) ⊆ L ∧ ({x, y, z} : Finset W).card = 3 ∧
      (epCut α β ({x, y, z} : Finset W)).card = 3 := by
  obtain ⟨hx, hy, hz, hxy, hyz, hxz, h1, h2, h3⟩ := ht
  have hTeq : ({x, y, z} : Finset W) = ({x} ∪ {y}) ∪ {z} := by
    ext w; simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]; tauto
  have hdxy : Disjoint ({x} : Finset W) {y} := Finset.disjoint_singleton.mpr hxy
  have hdxz : Disjoint ({x} : Finset W) {z} := Finset.disjoint_singleton.mpr hxz
  have hdyz : Disjoint ({y} : Finset W) {z} := Finset.disjoint_singleton.mpr hyz
  have hd2 : Disjoint ({x} ∪ {y} : Finset W) {z} :=
    Finset.disjoint_union_left.mpr ⟨hdxz, hdyz⟩
  have hcard : ({x, y, z} : Finset W).card = 3 := by
    rw [hTeq, Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hdxy,
      Finset.card_singleton, Finset.card_singleton, Finset.card_singleton]
  have hTL : ({x, y, z} : Finset W) ⊆ L := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact hx
    · exact hy
    · exact hz
  refine ⟨hTL, hcard, ?_⟩
  have e1 : 1 ≤ (epBtw α β {x} {y}).card :=
    Finset.card_pos.mpr ⟨exy, ep_edge_btw α β x y exy hxy h1⟩
  have e2 : 1 ≤ (epBtw α β {z} {y}).card :=
    Finset.card_pos.mpr ⟨eyz, by rw [ep_btw_comm]; exact ep_edge_btw α β y z eyz hyz h2⟩
  have e3 : 1 ≤ (epBtw α β {z} {x}).card :=
    Finset.card_pos.mpr ⟨ezx, ep_edge_btw α β z x ezx (Ne.symm hxz) h3⟩
  have c1 := ep_cut_union α β {x} {y} hdxy
  rw [h.2 x hx, h.2 y hy] at c1
  have c2 := ep_cut_union α β ({x} ∪ {y}) {z} hd2
  rw [h.2 z hz, ← hTeq] at c2
  have c3 := ep_btw_add α β {z} {x} {y} hdxz.symm hdyz.symm hdxy
  rw [ep_btw_comm α β {z} ({x} ∪ {y})] at c3
  have c4 := ep_cut_ge_two α β L hb hconn _ hTL (Finset.card_pos.mp (by omega))
    (fun h' => by rw [h'] at hcard; omega)
  have c5 := epD_cut_parity α β L h _ hTL
  rw [hcard] at c5
  omega

/-- Two vertices are adjacent. -/
def EpAdj {W E : Type*} (α β : E → W) (u v : W) : Prop :=
  ∃ g, (α g = u ∧ β g = v) ∨ (α g = v ∧ β g = u)

open Classical in
/-- A triangle is **irrelevant** if neighbours outside the triangle of its vertices are never
adjacent, and those of two distinct vertices of the triangle are distinct. -/
def EpIrrelevant {W E : Type*} (α β : E → W) (x y z : W) : Prop :=
  ∀ u ∈ ({x, y, z} : Finset W), ∀ v ∈ ({x, y, z} : Finset W),
    ∀ a b, a ∉ ({x, y, z} : Finset W) → b ∉ ({x, y, z} : Finset W) →
      EpAdj α β u a → EpAdj α β v b → (u ≠ v → a ≠ b) ∧ ¬EpAdj α β a b

set_option maxHeartbeats 800000 in
open Classical in
/-- **Corollary 16, first part.** Every relevant triangle meets a member of a family of
pairwise disjoint pool sets of maximum coverage. -/
theorem ep_relevant_meets {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (h : EpCubicD α β L) (hb : EpBridgeless α β L) (hconn : EpConnected α β L)
    (hbig : 12 ≤ L.card) (𝒴 : Finset (Finset W)) (hfam : EpTwigFam α β L 𝒴)
    (hmax : ∀ 𝒴', EpTwigFam α β L 𝒴' → (𝒴'.biUnion id).card ≤ (𝒴.biUnion id).card)
    (x y z : W) (exy eyz ezx : E) (ht : EpTriangle α β L x y z exy eyz ezx)
    (hrel : ¬EpIrrelevant α β x y z) :
    ¬Disjoint ({x, y, z} : Finset W) (𝒴.biUnion id) := by
  obtain ⟨hTL, hT3, hTcut⟩ := ep_triangle_cut α β L h hb hconn (by omega) x y z exy eyz ezx ht
  unfold EpIrrelevant at hrel
  push_neg at hrel
  obtain ⟨u, hu, v, hv, a, b, haT, hbT, ⟨g, hg⟩, ⟨g', hg'⟩, hab⟩ := hrel
  -- the outside ends are vertices of the graph
  have hlive : ∀ (f : E) (p q : W), p ∈ L → ((α f = p ∧ β f = q) ∨ (α f = q ∧ β f = p)) →
      q ∈ L := by
    intro f p q hp hf
    rcases h.1 f with ⟨l1, l2, -⟩ | ⟨l1, l2⟩
    · rcases hf with ⟨f1, f2⟩ | ⟨f1, f2⟩
      · exact f2 ▸ l2
      · exact f1 ▸ l1
    · rcases hf with ⟨f1, f2⟩ | ⟨f1, f2⟩
      · exact absurd (f1 ▸ hp) l1
      · exact absurd (f2 ▸ hp) (l2 ▸ l1)
  have haL : a ∈ L := hlive g u a (hTL hu) hg
  have hbL : b ∈ L := hlive g' v b (hTL hv) hg'
  have hga : g ∈ epBtw α β {a} ({x, y, z} : Finset W) := by
    rw [mem_epBtw]
    rcases hg with ⟨f1, f2⟩ | ⟨f1, f2⟩
    · exact Or.inr ⟨f1 ▸ hu, by rw [f2]; exact Finset.mem_singleton_self a⟩
    · exact Or.inl ⟨by rw [f1]; exact Finset.mem_singleton_self a, f2 ▸ hu⟩
  have hgb : g' ∈ epBtw α β {b} ({x, y, z} : Finset W) := by
    rw [mem_epBtw]
    rcases hg' with ⟨f1, f2⟩ | ⟨f1, f2⟩
    · exact Or.inr ⟨f1 ▸ hv, by rw [f2]; exact Finset.mem_singleton_self b⟩
    · exact Or.inl ⟨by rw [f1]; exact Finset.mem_singleton_self b, f2 ▸ hv⟩
  by_cases hab' : a = b
  · -- a diamond
    subst hab'
    have huv : u ≠ v := by
      intro huv
      obtain ⟨g'', hg''⟩ := hab (fun h' => absurd huv h')
      have hloop : β g'' = α g'' := by
        rcases hg'' with ⟨f1, f2⟩ | ⟨f1, f2⟩ <;> rw [f1, f2]
      have hα : α g'' = a := by
        rcases hg'' with ⟨f1, f2⟩ | ⟨f1, f2⟩
        · exact f1
        · exact f1
      rcases h.1 g'' with ⟨-, -, l3⟩ | ⟨l1, -⟩
      · exact l3 hloop.symm
      · exact l1 (hα ▸ haL)
    have hgg' : g ≠ g' := by
      intro he
      subst he
      have hau : a ≠ u := fun h' => haT (h' ▸ hu)
      have hav : a ≠ v := fun h' => haT (h' ▸ hv)
      rcases hg with ⟨f1, f2⟩ | ⟨f1, f2⟩ <;> rcases hg' with ⟨f3, f4⟩ | ⟨f3, f4⟩
      · exact huv (f1.symm.trans f3)
      · exact hau (f3.symm.trans f1)
      · exact hav (f1.symm.trans f3)
      · exact huv (f2.symm.trans f4)
    refine ep_twigFam_meets_diamond α β L h hb hconn hbig 𝒴 hfam hmax _ hTL hT3 hTcut a haL haT ?_
    have : ({g, g'} : Finset E) ⊆ epBtw α β {a} ({x, y, z} : Finset W) := by
      intro f hf
      rcases Finset.mem_insert.mp hf with rfl | hf
      · exact hga
      · rw [Finset.mem_singleton.mp hf]; exact hgb
    have h2 := Finset.card_le_card this
    rw [Finset.card_pair hgg'] at h2
    exact h2
  · obtain ⟨g'', hg''⟩ := hab (fun _ => hab')
    refine ep_twigFam_meets_house α β L h hb hconn hbig 𝒴 hfam hmax _ hTL hT3 hTcut a b haL hbL
      haT hbT hab' (Finset.card_pos.mpr ⟨g'', ?_⟩) (Finset.card_pos.mpr ⟨g, hga⟩)
      (Finset.card_pos.mpr ⟨g', hgb⟩)
    rw [mem_epBtw]
    simp only [Finset.mem_singleton]
    exact hg''

/-- The ends of an edge crossing exactly the singletons `{p}` and `{q}`. -/
lemma ep_edge_ends {W E : Type*} [Fintype E] (α β : E → W) (p q : W) (e : E) (hpq : p ≠ q)
    (he : ∀ w, epCross α β {w} e ↔ w = p ∨ w = q) :
    (α e = p ∧ β e = q) ∨ (α e = q ∧ β e = p) := by
  have := ep_edge_btw α β p q e hpq he
  rw [mem_epBtw] at this
  simpa only [Finset.mem_singleton] using this

lemma ep_edge_cross {W E : Type*} (α β : E → W) (p q : W) (e : E) (hpq : p ≠ q)
    (he : (α e = p ∧ β e = q) ∨ (α e = q ∧ β e = p)) (w : W) :
    epCross α β {w} e ↔ w = p ∨ w = q := by
  rw [epCross_singleton]
  rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
  · constructor
    · rintro (⟨a, -⟩ | ⟨-, b⟩)
      · exact Or.inl a.symm
      · exact Or.inr b.symm
    · rintro (hw | hw)
      · exact Or.inl ⟨hw.symm, fun h'' => hpq (hw.symm.trans h''.symm)⟩
      · exact Or.inr ⟨fun h'' => hpq (h''.trans hw), hw.symm⟩
  · constructor
    · rintro (⟨a, -⟩ | ⟨-, b⟩)
      · exact Or.inr a.symm
      · exact Or.inl b.symm
    · rintro (hw | hw)
      · exact Or.inr ⟨fun h'' => hpq (hw.symm.trans h''.symm), hw.symm⟩
      · exact Or.inl ⟨hw.symm, fun h'' => hpq (h''.trans hw)⟩

lemma EpTriangle.rot {W E : Type*} {α β : E → W} {L : Finset W} {x y z : W}
    {exy eyz ezx : E} (ht : EpTriangle α β L x y z exy eyz ezx) :
    EpTriangle α β L y z x eyz ezx exy := by
  obtain ⟨hx, hy, hz, hxy, hyz, hxz, h1, h2, h3⟩ := ht
  exact ⟨hy, hz, hx, hyz, Ne.symm hxz, Ne.symm hxy, h2, h3, h1⟩

open Classical in
/-- Contraction of an irrelevant triangle. -/
def EpTriStep {W E : Type*} (α β : E → W) (L : Finset W) (α' β' : E → W) (L' : Finset W) :
    Prop :=
  ∃ x y z exy eyz ezx, EpTriangle α β L x y z exy eyz ezx ∧ EpIrrelevant α β x y z ∧
    α' = epConA α β ({x, y, z} : Finset W) x y ∧ β' = epConB α β ({x, y, z} : Finset W) x y ∧
    L' = epL' L ({x, y, z} : Finset W) x

/-- Repeated contraction of irrelevant triangles. -/
def EpTriReach {W E : Type*} (α β : E → W) (L : Finset W) (α' β' : E → W) (L' : Finset W) :
    Prop :=
  Relation.ReflTransGen
    (fun a b : (E → W) × (E → W) × Finset W => EpTriStep a.1 a.2.1 a.2.2 b.1 b.2.1 b.2.2)
    (α, β, L) (α', β', L')

/-- A multigraph is **pruned** if it has no irrelevant triangle. -/
def EpPruned {W E : Type*} (α β : E → W) (L : Finset W) : Prop :=
  ∀ x y z exy eyz ezx, EpTriangle α β L x y z exy eyz ezx → ¬EpIrrelevant α β x y z

open Classical in
/-- Ends of an edge of the contracted graph joining two vertices outside the contracted set. -/
lemma epCon_ends_out {W E : Type*} (α β : E → W) (X : Finset W) (x₀ x₁ : W) (hx₀ : x₀ ∈ X)
    (hx₁ : x₁ ∈ X) (e : E) (p q : W) (hp : p ∉ X) (hq : q ∉ X)
    (he : epConA α β X x₀ x₁ e = p ∧ epConB α β X x₀ x₁ e = q) : α e = p ∧ β e = q := by
  unfold epConA epConB epRho at he
  by_cases hin : α e ∈ X ∧ β e ∈ X
  · rw [if_pos hin] at he
    exact absurd (he.1 ▸ hx₁) hp
  · rw [if_neg hin, if_neg hin] at he
    obtain ⟨h1, h2⟩ := he
    by_cases ha : α e ∈ X
    · rw [if_pos ha] at h1; exact absurd (h1 ▸ hx₀) hp
    · by_cases hb : β e ∈ X
      · rw [if_pos hb] at h2; exact absurd (h2 ▸ hx₀) hq
      · rw [if_neg ha] at h1; rw [if_neg hb] at h2; exact ⟨h1, h2⟩

open Classical in
/-- Ends of an edge of the contracted graph at the new vertex. -/
lemma epCon_ends_new {W E : Type*} (α β : E → W) (X : Finset W) (x₀ x₁ : W) (hx₀ : x₀ ∈ X)
    (hne : x₁ ≠ x₀) (e : E) (q : W) (hq : q ∉ X)
    (he : (epConA α β X x₀ x₁ e = x₀ ∧ epConB α β X x₀ x₁ e = q) ∨
      (epConA α β X x₀ x₁ e = q ∧ epConB α β X x₀ x₁ e = x₀)) :
    ∃ u ∈ X, EpAdj α β u q := by
  unfold epConA epConB epRho at he
  by_cases hin : α e ∈ X ∧ β e ∈ X
  · simp only [if_pos hin] at he
    rcases he with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact absurd h1 hne
    · exact absurd h2 hne
  · rw [if_neg hin, if_neg hin] at he
    rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hb : β e ∉ X := fun hb => by rw [if_pos hb] at h2; exact hq (h2 ▸ hx₀)
      rw [if_neg hb] at h2
      have ha : α e ∈ X := by
        by_contra ha
        rw [if_neg ha] at h1
        exact ha (h1 ▸ hx₀)
      exact ⟨α e, ha, e, Or.inl ⟨rfl, h2⟩⟩
    · have ha : α e ∉ X := fun ha => by rw [if_pos ha] at h1; exact hq (h1 ▸ hx₀)
      rw [if_neg ha] at h1
      have hb : β e ∈ X := by
        by_contra hb
        rw [if_neg hb] at h2
        exact hb (h2 ▸ hx₀)
      exact ⟨β e, hb, e, Or.inr ⟨h1, rfl⟩⟩

open Classical in
/-- After the contraction of an irrelevant triangle the new vertex lies in no triangle. -/
lemma ep_tri_new_not_in_triangle {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (x y z : W) (hx : x ∈ ({x, y, z} : Finset W)) (hyx : y ≠ x) (hy : y ∈ ({x, y, z} : Finset W))
    (hirr : EpIrrelevant α β x y z) (p q r : W) (e1 e2 e3 : E)
    (ht : EpTriangle (epConA α β ({x, y, z} : Finset W) x y) (epConB α β ({x, y, z} : Finset W) x y)
      (epL' L ({x, y, z} : Finset W) x) p q r e1 e2 e3) : p ≠ x := by
  intro hpx
  obtain ⟨hp, hq, hr, hpq, hqr, hpr, h1, h2, h3⟩ := ht
  subst hpx
  have hout : ∀ w, w ∈ epL' L ({p, y, z} : Finset W) p → w ≠ p → w ∉ ({p, y, z} : Finset W) := by
    intro w hw hwp
    unfold epL' at hw
    rcases Finset.mem_insert.mp hw with h' | h'
    · exact absurd h' hwp
    · exact (Finset.mem_sdiff.mp h').2
  have hqT := hout q hq (Ne.symm hpq)
  have hrT := hout r hr (Ne.symm hpr)
  obtain ⟨u, hu, hadj1⟩ := epCon_ends_new α β _ p y hx hyx e1 q hqT
    (ep_edge_ends _ _ p q e1 hpq h1)
  obtain ⟨v, hv, hadj2⟩ := epCon_ends_new α β _ p y hx hyx e3 r hrT
    ((ep_edge_ends _ _ r p e3 (Ne.symm hpr) h3).symm)
  have hadj3 : EpAdj α β q r := by
    rcases ep_edge_ends _ _ q r e2 hqr h2 with h' | h'
    · exact ⟨e2, Or.inl (epCon_ends_out α β _ p y hx hy e2 q r hqT hrT h')⟩
    · exact ⟨e2, Or.inr (epCon_ends_out α β _ p y hx hy e2 r q hrT hqT h')⟩
  exact (hirr u hu v hv q r hqT hrT hadj1 hadj2).2 hadj3

open Classical in
/-- After the contraction of an irrelevant triangle, every triangle avoids the new vertex and
is a triangle of the original multigraph. -/
theorem ep_tri_contract_triangle {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (x y z : W) (hyx : y ≠ x) (hirr : EpIrrelevant α β x y z) (p q r : W) (e1 e2 e3 : E)
    (ht : EpTriangle (epConA α β ({x, y, z} : Finset W) x y) (epConB α β ({x, y, z} : Finset W) x y)
      (epL' L ({x, y, z} : Finset W) x) p q r e1 e2 e3) :
    p ≠ x ∧ q ≠ x ∧ r ≠ x ∧ EpTriangle α β L p q r e1 e2 e3 := by
  have hx : x ∈ ({x, y, z} : Finset W) := Finset.mem_insert_self _ _
  have hy : y ∈ ({x, y, z} : Finset W) :=
    Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hpx := ep_tri_new_not_in_triangle α β L x y z hx hyx hy hirr p q r e1 e2 e3 ht
  have hqx := ep_tri_new_not_in_triangle α β L x y z hx hyx hy hirr q r p e2 e3 e1 ht.rot
  have hrx := ep_tri_new_not_in_triangle α β L x y z hx hyx hy hirr r p q e3 e1 e2 ht.rot.rot
  refine ⟨hpx, hqx, hrx, ?_⟩
  obtain ⟨hp, hq, hr, hpq, hqr, hpr, h1, h2, h3⟩ := ht
  have hout : ∀ w, w ∈ epL' L ({x, y, z} : Finset W) x → w ≠ x →
      w ∈ L ∧ w ∉ ({x, y, z} : Finset W) := by
    intro w hw hwp
    unfold epL' at hw
    rcases Finset.mem_insert.mp hw with h' | h'
    · exact absurd h' hwp
    · exact Finset.mem_sdiff.mp h'
  obtain ⟨hpL, hpT⟩ := hout p hp hpx
  obtain ⟨hqL, hqT⟩ := hout q hq hqx
  obtain ⟨hrL, hrT⟩ := hout r hr hrx
  have hedge : ∀ (e : E) (a b : W), a ≠ b → a ∉ ({x, y, z} : Finset W) →
      b ∉ ({x, y, z} : Finset W) →
      (∀ w, epCross (epConA α β ({x, y, z} : Finset W) x y)
        (epConB α β ({x, y, z} : Finset W) x y) {w} e ↔ w = a ∨ w = b) →
      ∀ w, epCross α β {w} e ↔ w = a ∨ w = b := by
    intro e a b hab ha hb he w
    apply ep_edge_cross α β a b e hab
    rcases ep_edge_ends _ _ a b e hab he with h' | h'
    · exact Or.inl (epCon_ends_out α β _ x y hx hy e a b ha hb h')
    · exact Or.inr (epCon_ends_out α β _ x y hx hy e b a hb ha h')
  exact ⟨hpL, hqL, hrL, hpq, hqr, hpr, hedge e1 p q hpq hpT hqT h1, hedge e2 q r hqr hqT hrT h2,
    hedge e3 r p (Ne.symm hpr) hrT hpT h3⟩

set_option maxHeartbeats 800000 in
open Classical in
/-- **Lemma 8** in invariant form: `New` is a set of vertices lying in no triangle. -/
theorem ep_prune_aux {W E : Type*} [Fintype E] : ∀ (n : ℕ) (α β : E → W) (L New : Finset W),
    L.card = n → New ⊆ L →
    (∀ x y z exy eyz ezx, EpTriangle α β L x y z exy eyz ezx → x ∉ New ∧ y ∉ New ∧ z ∉ New) →
    ∃ α' β' L', EpTriReach α β L α' β' L' ∧ EpPruned α' β' L' ∧
      3 * New.card + (L \ New).card ≤ 3 * L'.card := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro α β L New hn hNew htri
    by_cases hp : EpPruned α β L
    · refine ⟨α, β, L, Relation.ReflTransGen.refl, hp, ?_⟩
      have := Finset.card_sdiff_add_card_eq_card hNew
      omega
    · unfold EpPruned at hp
      push_neg at hp
      obtain ⟨x, y, z, exy, eyz, ezx, ht, hirr⟩ := hp
      obtain ⟨hxN, hyN, hzN⟩ := htri x y z exy eyz ezx ht
      have ⟨hx, hy, hz, hxy, hyz, hxz, _, _, _⟩ := ht
      have hT3 : ({x, y, z} : Finset W).card = 3 :=
        Finset.card_eq_three.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩
      have hTmem : ∀ w, w ∈ ({x, y, z} : Finset W) ↔ w = x ∨ w = y ∨ w = z := by
        intro w; simp only [Finset.mem_insert, Finset.mem_singleton]
      have hTL : ({x, y, z} : Finset W) ⊆ L := by
        intro w hw
        rcases (hTmem w).mp hw with rfl | rfl | rfl
        · exact hx
        · exact hy
        · exact hz
      have hTN : ∀ w, w ∈ ({x, y, z} : Finset W) → w ∉ New := by
        intro w hw
        rcases (hTmem w).mp hw with rfl | rfl | rfl
        · exact hxN
        · exact hyN
        · exact hzN
      have hxT : x ∈ ({x, y, z} : Finset W) := (hTmem x).mpr (Or.inl rfl)
      have hstep : EpTriStep α β L (epConA α β ({x, y, z} : Finset W) x y)
          (epConB α β ({x, y, z} : Finset W) x y) (epL' L ({x, y, z} : Finset W) x) :=
        ⟨x, y, z, exy, eyz, ezx, ht, hirr, rfl, rfl, rfl⟩
      have hL₁ : (epL' L ({x, y, z} : Finset W) x).card + 2 = L.card := by
        unfold epL'
        rw [Finset.card_insert_of_notMem (fun h' => (Finset.mem_sdiff.mp h').2 hxT),
          Finset.card_sdiff_of_subset hTL, hT3]
        have := Finset.card_le_card hTL
        omega
      obtain ⟨α', β', L', hreach, hpr, hcount⟩ :=
        ih (epL' L ({x, y, z} : Finset W) x).card (by omega) _ _ _ (insert x New) rfl
          (by
            intro w hw
            unfold epL'
            rcases Finset.mem_insert.mp hw with rfl | hw
            · exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr
                ⟨hNew hw, fun h' => hTN w h' hw⟩))
          (by
            intro p q r e1 e2 e3 ht'
            obtain ⟨a1, a2, a3, a4⟩ := ep_tri_contract_triangle α β L x y z (Ne.symm hxy) hirr
              p q r e1 e2 e3 ht'
            obtain ⟨b1, b2, b3⟩ := htri p q r e1 e2 e3 a4
            exact ⟨fun h' => (Finset.mem_insert.mp h').elim a1 b1,
              fun h' => (Finset.mem_insert.mp h').elim a2 b2,
              fun h' => (Finset.mem_insert.mp h').elim a3 b3⟩)
      refine ⟨α', β', L', Relation.ReflTransGen.head hstep hreach, hpr, ?_⟩
      have hset : epL' L ({x, y, z} : Finset W) x \ insert x New =
          (L \ New) \ ({x, y, z} : Finset W) := by
        unfold epL'
        ext w
        simp only [Finset.mem_sdiff, Finset.mem_insert]
        constructor
        · rintro ⟨h1 | h1, h2⟩
          · exact absurd (Or.inl h1) h2
          · exact ⟨⟨h1.1, fun h' => h2 (Or.inr h')⟩, h1.2⟩
        · rintro ⟨⟨h1, h2⟩, h3⟩
          exact ⟨Or.inr ⟨h1, h3⟩, fun h' => h'.elim (fun h'' => h3 (Or.inl h'')) h2⟩
      have hsub : ({x, y, z} : Finset W) ⊆ L \ New := fun w hw =>
        Finset.mem_sdiff.mpr ⟨hTL hw, hTN w hw⟩
      rw [hset, Finset.card_sdiff_of_subset hsub, hT3,
        Finset.card_insert_of_notMem hxN] at hcount
      have := Finset.card_le_card hsub
      omega

/-- **Corollary 9.** Repeatedly contracting irrelevant triangles gives a pruned multigraph with
at least a third of the vertices. -/
theorem ep_prune {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) :
    ∃ α' β' L', EpTriReach α β L α' β' L' ∧ EpPruned α' β' L' ∧ L.card ≤ 3 * L'.card := by
  classical
  obtain ⟨α', β', L', h1, h2, h3⟩ := ep_prune_aux L.card α β L ∅ rfl (Finset.empty_subset _)
    (fun _ _ _ _ _ _ _ => ⟨Finset.notMem_empty _, Finset.notMem_empty _, Finset.notMem_empty _⟩)
  refine ⟨α', β', L', h1, h2, ?_⟩
  rw [Finset.card_empty, Finset.sdiff_empty] at h3
  omega

set_option maxHeartbeats 800000 in
open Classical in
/-- **Hubs of a maximum decomposition.** In a `𝒴`-maximum decomposition, a node with a nonempty
atom that is not a member of `𝒴` has a cyclically 4-edge-connected hub: a multigraph reachable
by cut-contractions that keeps the atom, has one more vertex for each contracted set with a cut
of size three, keeps the edges inside the atom and reflects burls avoiding the new edges. -/
theorem ep_max_decomp_hub {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (r : W)
    (𝒮 𝒴 : Finset (Finset W)) (h : EpCubicD α β L) (hb : EpBridgeless α β L)
    (hconn : EpConnected α β L) (hr : r ∈ L) (hdec : EpDecomp α β L r 𝒮)
    (href : EpRefines L r 𝒮 𝒴)
    (hmax : ∀ 𝒮', EpDecomp α β L r 𝒮' → EpRefines L r 𝒮' 𝒴 → 𝒮'.card ≤ 𝒮.card)
    (N : Finset W) (hN : N ∈ insert L 𝒮) (hne : (epAtom 𝒮 N).Nonempty)
    (hA : epAtom 𝒮 N ∉ 𝒴) :
    ∃ (α' β' : E → W) (L' : Finset W) (newE : Finset E),
      EpReach α β L α' β' L' ∧ EpCyc4 α' β' L' ∧ epAtom 𝒮 N ⊆ L' ∧ L' ⊆ L ∧
      L'.card = (epAtom 𝒮 N).card +
        ((epHubFam 𝒮 L N).filter (fun C => (epCut α β C).card = 3)).card ∧
      (∀ g, α g ∈ epAtom 𝒮 N → β g ∈ epAtom 𝒮 N → α' g = α g ∧ β' g = β g) ∧
      (∀ Z, Z ⊆ epAtom 𝒮 N → (∀ g ∈ newE, ¬(α' g ∈ Z ∧ β' g ∈ Z)) → EpBurl α' β' Z →
        EpBurl α β Z ∧ (epCut α β Z).card = (epCut α' β' Z).card) := by
  obtain ⟨a, ha⟩ := hne
  obtain ⟨hfam, hdis, hAeq⟩ := ep_hubFam_spec α β L r 𝒮 h hr hdec N hN
  have haL : a ∈ L := by
    have : a ∈ L \ (epHubFam 𝒮 L N).biUnion id := by rw [hAeq]; exact ha
    exact (Finset.mem_sdiff.mp this).1
  obtain ⟨α', β', L', newE, hreach, hsub, hsubL, hcard, hfix, hburl, hlift⟩ :=
    ep_hub_exists (epHubFam 𝒮 L N).card α β L (epHubFam 𝒮 L N) a rfl h hb hconn haL
      (fun C hC => ⟨(hfam C hC).1, (hfam C hC).2.1, (hfam C hC).2.2.1 a ha, (hfam C hC).2.2.2⟩)
      hdis
  obtain ⟨h', hb', hconn', -⟩ := hreach.preserves h hb hconn
  have h4 := ep_max_decomp_cyc4 α β L r 𝒮 𝒴 h hr hdec href hmax N hN hA α' β' L' h' hb' hconn'
    hlift
  rw [hAeq] at hsub hcard hfix hburl
  exact ⟨α', β', L', newE, hreach, h4, hsub, hsubL, hcard, hfix, hburl⟩

set_option maxHeartbeats 1600000 in
open Classical in
/-- **Monotonicity of burls.** A set containing a burl is a burl. -/
theorem ep_burl_mono {W E : Type*} [Fintype E] (α β : E → W) (X Y : Finset W) (hXY : X ⊆ Y)
    (hnl : ∀ e, α e ∈ Y → α e ≠ β e) (hX : EpBurl α β X) : EpBurl α β Y := by
  intro p hp
  obtain ⟨hp0, hpLM, hp1, hpbal⟩ := hp
  have hF : ∀ (N : Finset E) (e : E), e ∈ N.filter (fun e => α e ∈ X ∨ β e ∈ X) ↔
      e ∈ N ∧ (α e ∈ X ∨ β e ∈ X) := fun N e => Finset.mem_filter
  have hin : ∀ c ∈ X, ∀ e, epCross α β {c} e → α e ∈ X ∨ β e ∈ X := by
    intro c hc e he
    rw [epCross_singleton] at he
    rcases he with ⟨h, -⟩ | ⟨-, h⟩
    · exact Or.inl (h ▸ hc)
    · exact Or.inr (h ▸ hc)
  -- restriction of a local matching of `Y` to `X`
  have hres : ∀ N, N ∈ epLM α β Y → N.filter (fun e => α e ∈ X ∨ β e ∈ X) ∈ epLM α β X := by
    intro N hN
    refine ⟨fun e he => ((hF N e).mp he).2, fun c hc => ?_⟩
    obtain ⟨e₀, ⟨h1, h2⟩, huniq⟩ := hN.2 c (hXY hc)
    exact ⟨e₀, ⟨(hF N e₀).mpr ⟨h1, hin c hc e₀ h2⟩, h2⟩,
      fun e he => huniq e ⟨((hF N e).mp he.1).1, he.2⟩⟩
  -- flip sets of the restriction are flip sets of the matching
  have halt : ∀ N, N ∈ epLM α β Y →
      epAltNum α β X (N.filter (fun e => α e ∈ X ∨ β e ∈ X)) ≤ epAltNum α β Y N := by
    intro N hN
    obtain ⟨D, hne, hDin, hflip, hdisj⟩ := epAltNum_spec α β X (N.filter (fun e => α e ∈ X ∨ β e ∈ X))
    refine epAlt_le_altNum' α β Y hnl N _ ⟨D, hne, fun i e he => ⟨hXY (hDin i e he).1,
      hXY (hDin i e he).2⟩, fun i => ⟨fun e he => ?_, fun c hc => ?_⟩, hdisj⟩
    · rcases Finset.mem_symmDiff.mp he with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hN.1 e h1
      · exact Or.inl (hXY (hDin i e h1).1)
    · by_cases hcX : c ∈ X
      · obtain ⟨e₀, ⟨h1, h2⟩, huniq⟩ := (hflip i).2 c hcX
        have key : ∀ e, epCross α β {c} e →
            (e ∈ symmDiff N (D i) ↔
              e ∈ symmDiff (N.filter (fun e => α e ∈ X ∨ β e ∈ X)) (D i)) := by
          intro e he
          rw [Finset.mem_symmDiff, Finset.mem_symmDiff, hF]
          have := hin c hcX e he
          tauto
        exact ⟨e₀, ⟨(key e₀ h2).mpr h1, h2⟩, fun e he => huniq e ⟨(key e he.2).mp he.1, he.2⟩⟩
      · obtain ⟨e₀, ⟨h1, h2⟩, huniq⟩ := hN.2 c hc
        have hnot : ∀ e, epCross α β {c} e → e ∉ D i := by
          intro e he heD
          rw [epCross_singleton] at he
          rcases he with ⟨h, -⟩ | ⟨-, h⟩
          · exact hcX (h ▸ (hDin i e heD).1)
          · exact hcX (h ▸ (hDin i e heD).2)
        have key : ∀ e, epCross α β {c} e → (e ∈ symmDiff N (D i) ↔ e ∈ N) := by
          intro e he
          rw [Finset.mem_symmDiff]
          have := hnot e he
          tauto
        exact ⟨e₀, ⟨(key e₀ h2).mpr h1, h2⟩, fun e he => huniq e ⟨(key e he.2).mp he.1, he.2⟩⟩
  -- the push-forward distribution
  obtain ⟨q, hq⟩ : ∃ q : Finset E → ℝ, ∀ N', q N' =
      ∑ N, if N.filter (fun e => α e ∈ X ∨ β e ∈ X) = N' then p N else 0 := ⟨_, fun _ => rfl⟩
  have hpush : ∀ g : Finset E → ℝ, ∑ N', q N' * g N' =
      ∑ N, p N * g (N.filter (fun e => α e ∈ X ∨ β e ∈ X)) := by
    intro g
    have h1 : ∀ N', q N' * g N' =
        ∑ N, (if N.filter (fun e => α e ∈ X ∨ β e ∈ X) = N' then p N * g N' else 0) := by
      intro N'
      rw [hq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun N _ => ?_
      split_ifs <;> simp
    rw [Finset.sum_congr rfl (fun N' _ => h1 N'), Finset.sum_comm]
    refine Finset.sum_congr rfl fun N _ => ?_
    rw [Finset.sum_eq_single (N.filter (fun e => α e ∈ X ∨ β e ∈ X))]
    · rw [if_pos rfl]
    · intro N' _ hne
      rw [if_neg (Ne.symm hne)]
    · intro h'; exact absurd (Finset.mem_univ _) h'
  have hqbal : EpBalanced α β X q := by
    refine ⟨fun N' => ?_, fun N' hN' => ?_, ?_, fun e he => ?_⟩
    · rw [hq]; exact Finset.sum_nonneg fun N _ => by split_ifs <;> [exact hp0 N; exact le_refl 0]
    · rw [hq] at hN'
      obtain ⟨N, -, hN⟩ := Finset.exists_ne_zero_of_sum_ne_zero hN'
      by_cases hc : N.filter (fun e => α e ∈ X ∨ β e ∈ X) = N'
      · rw [if_pos hc] at hN
        rw [← hc]; exact hres N (hpLM N hN)
      · rw [if_neg hc] at hN; exact absurd rfl hN
    · have := hpush (fun _ => 1)
      simp only [mul_one] at this
      rw [this, hp1]
    · rw [hpush (fun N' => epInd N' e), ← hpbal e (he.elim (fun h => Or.inl (hXY h))
        (fun h => Or.inr (hXY h)))]
      refine Finset.sum_congr rfl fun N _ => ?_
      congr 1
      unfold epInd
      by_cases heN : e ∈ N
      · rw [if_pos ((hF N e).mpr ⟨heN, he⟩), if_pos heN]
      · rw [if_neg (fun h' => heN ((hF N e).mp h').1), if_neg heN]
  have h3 := hX q hqbal
  rw [hpush (fun N' => (epAltNum α β X N' : ℝ))] at h3
  refine h3.trans (Finset.sum_le_sum fun N _ => ?_)
  by_cases hpN : p N = 0
  · rw [hpN, zero_mul, zero_mul]
  · exact mul_le_mul_of_nonneg_left (by exact_mod_cast halt N (hpLM N hpN)) (hp0 N)

open Classical in
/-- An edge of a 2-cut contraction whose first end is a kept vertex has its original ends. -/
lemma ep2_ends_keep {W E : Type*} (α β : E → W) (X : Finset W) (e e' : E) (x₁ : W)
    (hx₁ : x₁ ∈ X) (g : E) (hg : g ≠ e) (hout : ep2A α β X e e' x₁ g ∉ X) :
    ep2A α β X e e' x₁ g = α g ∧ ep2B α β X e e' x₁ g = β g := by
  have hA : ep2A α β X e e' x₁ g = if g = e' ∨ (α g ∈ X ∧ β g ∈ X) then x₁ else α g := by
    unfold ep2A; rw [if_neg hg]
  have hB : ep2B α β X e e' x₁ g = if g = e' ∨ (α g ∈ X ∧ β g ∈ X) then x₁ else β g := by
    unfold ep2B; rw [if_neg hg]
  by_cases hc : g = e' ∨ (α g ∈ X ∧ β g ∈ X)
  · rw [hA, if_pos hc] at hout; exact absurd hx₁ hout
  · rw [hA, hB, if_neg hc, if_neg hc]; exact ⟨rfl, rfl⟩

open Classical in
lemma ep2_ends_keep' {W E : Type*} (α β : E → W) (X : Finset W) (e e' : E) (x₁ : W)
    (g : E) (hg : g ≠ e) (hg' : g ≠ e') (hin : ¬(α g ∈ X ∧ β g ∈ X)) :
    ep2A α β X e e' x₁ g = α g ∧ ep2B α β X e e' x₁ g = β g := by
  unfold ep2A ep2B
  rw [if_neg hg, if_neg hg, if_neg (fun h' => h'.elim hg' hin), if_neg (fun h' => h'.elim hg' hin)]
  exact ⟨rfl, rfl⟩

/-- A perfect or near-perfect matching of the part `X` between two 2-cuts: all edges except
the marker `e` lie inside `X`; either `e` is absent and every vertex of `X` is covered once, or
`e` is present, and every vertex except `u`, `u'` is covered once while `u`, `u'` are not
covered. -/
def EpSand {W E : Type*} (α β : E → W) (X : Finset W) (e : E) (u u' : W) (P : Finset E) :
    Prop :=
  (∀ g ∈ P, g ≠ e → α g ∈ X ∧ β g ∈ X) ∧
    ((e ∉ P ∧ ∀ c ∈ X, ∃! g, (g ∈ P ∧ g ≠ e) ∧ epCross α β {c} g) ∨
     (e ∈ P ∧ u ≠ u' ∧ (∀ c ∈ X, c ≠ u → c ≠ u' → ∃! g, (g ∈ P ∧ g ≠ e) ∧ epCross α β {c} g) ∧
       ∀ g ∈ P, g ≠ e → ¬epCross α β {u} g ∧ ¬epCross α β {u'} g))

set_option maxHeartbeats 3200000 in
open Classical in
/-- **Sandwich lemma.** Let `A`, `B` be disjoint sets with cuts `{f, f'}` and `{e, e'}` and no
edge between them. Then the part in between has two different matchings, each perfect or
missing exactly the ends of `e` and `e'`. -/
theorem ep_sandwich {W E : Type*} [Fintype E] (α β : E → W) (L A B : Finset W)
    (f f' e e' : E) (a₁ b₁ : W) (h : EpCubicD α β L) (hb : EpBridgeless α β L)
    (hAL : A ⊆ L) (hBL : B ⊆ L) (hAB : ∀ w, w ∈ A → w ∉ B) (ha₁ : a₁ ∈ A) (hb₁ : b₁ ∈ B)
    (hff' : f ≠ f') (hee' : e ≠ e') (hcutA : ∀ g, epCross α β A g ↔ g = f ∨ g = f')
    (hcutB : ∀ g, epCross α β B g ↔ g = e ∨ g = e')
    (hno : ∀ g, ¬(α g ∈ A ∧ β g ∈ B) ∧ ¬(α g ∈ B ∧ β g ∈ A)) :
    ∃ P P' : Finset E, P ≠ P' ∧
      EpSand α β ((L \ A) \ B) e (epOut α β B e) (epOut α β B e') P ∧
      EpSand α β ((L \ A) \ B) e (epOut α β B e) (epOut α β B e') P' := by
  -- an edge does not cross both `A` and `B`
  have hnoboth : ∀ g, epCross α β A g → ¬epCross α β B g := by
    intro g hA hB
    unfold epCross at hA hB
    have := hno g
    have h1 := hAB (α g)
    have h2 := hAB (β g)
    tauto
  have hfe : f ≠ e ∧ f ≠ e' := by
    have := hnoboth f ((hcutA f).mpr (Or.inl rfl))
    rw [hcutB] at this
    exact ⟨fun h' => this (Or.inl h'), fun h' => this (Or.inr h')⟩
  have hef : ∀ g, (g = e ∨ g = e') → g ≠ f ∧ g ≠ f' ∧ ¬(α g ∈ A ∧ β g ∈ A) := by
    intro g hg
    have hB := (hcutB g).mpr hg
    have hA : ¬epCross α β A g := fun h' => hnoboth g h' hB
    rw [hcutA] at hA
    refine ⟨fun h' => hA (Or.inl h'), fun h' => hA (Or.inr h'), fun h' => ?_⟩
    unfold epCross at hB
    have h1 := hAB (α g) h'.1
    have h2 := hAB (β g) h'.2
    tauto
  -- first contraction
  have hfout := epOut_ends α β A f ((hcutA f).mpr (Or.inl rfl))
  have hf'out := epOut_ends α β A f' ((hcutA f').mpr (Or.inr rfl))
  have houtB : ∀ g, epCross α β A g → epOut α β A g ∉ B := by
    intro g hg hB
    obtain ⟨-, x, hx, hends⟩ := epOut_ends α β A g hg
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact (hno g).1 ⟨h1 ▸ hx, h2 ▸ hB⟩
    · exact (hno g).2 ⟨h1 ▸ hB, h2 ▸ hx⟩
  obtain ⟨h', hb'⟩ := ep2_cubic α β L A f f' a₁ h hb hAL ha₁ hff' hcutA
  have hcut' : ∀ g, epCross (ep2A α β A f f' a₁) (ep2B α β A f f' a₁) B g ↔ g = e ∨ g = e' := by
    intro g
    rw [ep2_cross α β A f f' a₁ hcutA B (fun w hw hwA => hAB w hwA hw) g]
    unfold ep2Lift
    rw [if_neg (houtB f' ((hcutA f').mpr (Or.inr rfl)))]
    exact hcutB g
  have hBL' : B ⊆ L \ A := fun w hw =>
    Finset.mem_sdiff.mpr ⟨hBL hw, fun hwA => hAB w hwA hw⟩
  obtain ⟨α', hα'⟩ : ∃ α' : E → W, α' = ep2A α β A f f' a₁ := ⟨_, rfl⟩
  obtain ⟨β', hβ'⟩ : ∃ β' : E → W, β' = ep2B α β A f f' a₁ := ⟨_, rfl⟩
  rw [← hα', ← hβ'] at h' hb' hcut'
  obtain ⟨h'', hb''⟩ := ep2_cubic α' β' (L \ A) B e e' b₁ h' hb' hBL' hb₁ hee' hcut'
  obtain ⟨α'', hα''⟩ : ∃ α'' : E → W, α'' = ep2A α' β' B e e' b₁ := ⟨_, rfl⟩
  obtain ⟨β'', hβ''⟩ : ∃ β'' : E → W, β'' = ep2B α' β' B e e' b₁ := ⟨_, rfl⟩
  rw [← hα'', ← hβ''] at h'' hb''
  -- ends of the edges in the two contractions
  have hkeep : ∀ g, g ≠ e → g ≠ f → α'' g ∈ (L \ A) \ B → α'' g = α g ∧ β'' g = β g := by
    intro g hge hgf hg
    have hgB : α'' g ∉ B := (Finset.mem_sdiff.mp hg).2
    have hgA : α'' g ∉ A := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hg).1).2
    rw [hα''] at hgB
    obtain ⟨k1, k2⟩ := ep2_ends_keep α' β' B e e' b₁ hb₁ g hge hgB
    rw [← hα''] at k1
    rw [← hβ''] at k2
    rw [k1, hα'] at hgA
    obtain ⟨k3, k4⟩ := ep2_ends_keep α β A f f' a₁ ha₁ g hgf hgA
    rw [← hα'] at k3
    rw [← hβ'] at k4
    exact ⟨k1.trans k3, k2.trans k4⟩
  have hekeep : ∀ g, (g = e ∨ g = e') → α' g = α g ∧ β' g = β g := by
    intro g hg
    obtain ⟨k1, k2, k3⟩ := hef g hg
    rw [hα', hβ']
    exact ep2_ends_keep' α β A f f' a₁ g k1 k2 k3
  have hout' : ∀ g, (g = e ∨ g = e') → epOut α' β' B g = epOut α β B g := by
    intro g hg
    unfold epOut
    rw [(hekeep g hg).1, (hekeep g hg).2]
  have hαe : α'' e = epOut α β B e := by
    rw [hα'']; unfold ep2A; rw [if_pos rfl]; exact hout' e (Or.inl rfl)
  have hβe : β'' e = epOut α β B e' := by
    rw [hβ'']; unfold ep2B; rw [if_pos rfl]; exact hout' e' (Or.inr rfl)
  -- `f` is a live edge of the double contraction
  have hfl : α'' f ∈ (L \ A) \ B := by
    have hαf : α' f = epOut α β A f := by rw [hα']; unfold ep2A; rw [if_pos rfl]
    obtain ⟨a1, a2, -, -⟩ := ep_cut_insert_card α β L A h hb hAL f f' hff' hcutA f (Or.inl rfl)
    have hnB : α' f ∉ B := by rw [hαf]; exact houtB f ((hcutA f).mpr (Or.inl rfl))
    have : α'' f = α' f := by
      rw [hα'']
      exact (ep2_ends_keep' α' β' B e e' b₁ f hfe.1 hfe.2 (fun h' => hnB h'.1)).1
    rw [this]
    exact Finset.mem_sdiff.mpr ⟨by rw [hαf]; exact Finset.mem_sdiff.mpr ⟨a1, a2⟩, hnB⟩
  obtain ⟨P, P', hP, hP', hne, hfP, hfP'⟩ :=
    epD_two_pm_avoiding α'' β'' ((L \ A) \ B) h'' hb'' f hfl
  have key : ∀ P : Finset E, P ∈ epPM α'' β'' ((L \ A) \ B) → f ∉ P →
      EpSand α β ((L \ A) \ B) e (epOut α β B e) (epOut α β B e') P := by
    intro P hP hfP
    have hlive : ∀ g ∈ P, α'' g ∈ (L \ A) \ B ∧ β'' g ∈ (L \ A) \ B := by
      intro g hg
      rcases h''.1 g with ⟨l1, l2, -⟩ | ⟨-, l2⟩
      · exact ⟨l1, l2⟩
      · exact absurd l2.symm (hP.1 g hg)
    have hends : ∀ g ∈ P, g ≠ e → α'' g = α g ∧ β'' g = β g := fun g hg hge =>
      hkeep g hge (fun h' => hfP (h' ▸ hg)) (hlive g hg).1
    have hcr : ∀ g ∈ P, g ≠ e → ∀ c, (epCross α β {c} g ↔ epCross α'' β'' {c} g) := by
      intro g hg hge c
      rw [epCross_singleton, epCross_singleton, (hends g hg hge).1, (hends g hg hge).2]
    refine ⟨fun g hg hge => ?_, ?_⟩
    · obtain ⟨k1, k2⟩ := hends g hg hge
      exact ⟨k1 ▸ (hlive g hg).1, k2 ▸ (hlive g hg).2⟩
    · by_cases heP : e ∈ P
      · right
        have hloop := hP.1 e heP
        have hecr : ∀ c, epCross α'' β'' {c} e ↔ c = epOut α β B e ∨ c = epOut α β B e' := by
          intro c; rw [ep_cross_ends α'' β'' e hloop c, hαe, hβe]
        rw [hαe, hβe] at hloop
        refine ⟨heP, hloop, fun c hc hcu hcu' => ?_, fun g hg hge => ?_⟩
        · obtain ⟨g₀, ⟨g1, g2⟩, huniq⟩ := hP.2 c hc
          have hg₀e : g₀ ≠ e := by
            intro h'; rw [h', hecr] at g2
            exact g2.elim hcu hcu'
          exact ⟨g₀, ⟨⟨g1, hg₀e⟩, (hcr g₀ g1 hg₀e c).mpr g2⟩,
            fun g hg => huniq g ⟨hg.1.1, (hcr g hg.1.1 hg.1.2 c).mp hg.2⟩⟩
        · have hu : epOut α β B e ∈ (L \ A) \ B := hαe ▸ (hlive e heP).1
          have hu' : epOut α β B e' ∈ (L \ A) \ B := hβe ▸ (hlive e heP).2
          constructor
          · intro hc
            obtain ⟨g₀, -, huniq⟩ := hP.2 _ hu
            have e1 := huniq g ⟨hg, (hcr g hg hge _).mp hc⟩
            have e2 := huniq e ⟨heP, (hecr _).mpr (Or.inl rfl)⟩
            exact hge (e1.trans e2.symm)
          · intro hc
            obtain ⟨g₀, -, huniq⟩ := hP.2 _ hu'
            have e1 := huniq g ⟨hg, (hcr g hg hge _).mp hc⟩
            have e2 := huniq e ⟨heP, (hecr _).mpr (Or.inr rfl)⟩
            exact hge (e1.trans e2.symm)
      · left
        refine ⟨heP, fun c hc => ?_⟩
        obtain ⟨g₀, ⟨g1, g2⟩, huniq⟩ := hP.2 c hc
        have hg₀e : g₀ ≠ e := fun h' => heP (h' ▸ g1)
        exact ⟨g₀, ⟨⟨g1, hg₀e⟩, (hcr g₀ g1 hg₀e c).mpr g2⟩,
          fun g hg => huniq g ⟨hg.1.1, (hcr g hg.1.1 hg.1.2 c).mp hg.2⟩⟩
  exact ⟨P, P', hne, key P hP hfP, key P' hP' hfP'⟩

/-- One side of the gluing of two sandwich matchings. -/
lemma ep_sand_side {W E : Type*} (α β : E → W) (X : Finset W) (e e' : E) (p p' : W)
    (P R : Finset E) (hP : EpSand α β X e p p' P) (hee' : e ≠ e')
    (hR1 : ∀ g ∈ P, g ≠ e → g ∈ R)
    (hR2 : ∀ g ∈ R, g ≠ e → g ≠ e' → g ∈ P ∨ (α g ∉ X ∧ β g ∉ X))
    (hRe : e ∈ R ↔ e ∈ P) (hRe' : e' ∈ R ↔ e ∈ P)
    (he : ∀ c ∈ X, epCross α β {c} e ↔ c = p) (he' : ∀ c ∈ X, epCross α β {c} e' ↔ c = p')
    (c : W) (hc : c ∈ X) : ∃! g, g ∈ R ∧ epCross α β {c} g := by
  have hout : ∀ g, epCross α β {c} g → ¬(α g ∉ X ∧ β g ∉ X) := by
    intro g hg hno
    rw [epCross_singleton] at hg
    rcases hg with ⟨h1, -⟩ | ⟨-, h1⟩
    · exact hno.1 (h1 ▸ hc)
    · exact hno.2 (h1 ▸ hc)
  obtain ⟨hin, hcase⟩ := hP
  rcases hcase with ⟨heP, hperf⟩ | ⟨heP, hpp', hdef, hnone⟩
  · obtain ⟨g₀, ⟨⟨g1, g2⟩, g3⟩, huniq⟩ := hperf c hc
    refine ⟨g₀, ⟨hR1 g₀ g1 g2, g3⟩, fun g hg => ?_⟩
    have hge : g ≠ e := fun h' => heP (hRe.mp (h' ▸ hg.1))
    have hge' : g ≠ e' := fun h' => heP (hRe'.mp (h' ▸ hg.1))
    rcases hR2 g hg.1 hge hge' with h' | h'
    · exact huniq g ⟨⟨h', hge⟩, hg.2⟩
    · exact absurd h' (hout g hg.2)
  · have hgen : ∀ g, g ∈ R → epCross α β {c} g → g ≠ e → g ≠ e' → g ∈ P := by
      intro g hg hcr hge hge'
      rcases hR2 g hg hge hge' with h' | h'
      · exact h'
      · exact absurd h' (hout g hcr)
    by_cases hcp : c = p
    · refine ⟨e, ⟨hRe.mpr heP, (he c hc).mpr hcp⟩, fun g hg => ?_⟩
      by_contra hge
      by_cases hge' : g = e'
      · rw [hge', he' c hc] at hg
        exact hpp' (hcp.symm.trans hg.2)
      · have := hgen g hg.1 hg.2 hge hge'
        exact (hnone g this hge).1 (hcp ▸ hg.2)
    · by_cases hcp' : c = p'
      · refine ⟨e', ⟨hRe'.mpr heP, (he' c hc).mpr hcp'⟩, fun g hg => ?_⟩
        by_contra hge'
        by_cases hge : g = e
        · rw [hge, he c hc] at hg
          exact hcp hg.2
        · have := hgen g hg.1 hg.2 hge hge'
          exact (hnone g this hge).2 (hcp' ▸ hg.2)
      · obtain ⟨g₀, ⟨⟨g1, g2⟩, g3⟩, huniq⟩ := hdef c hc hcp hcp'
        refine ⟨g₀, ⟨hR1 g₀ g1 g2, g3⟩, fun g hg => ?_⟩
        have hge : g ≠ e := fun h' => hcp ((he c hc).mp (h' ▸ hg.2))
        have hge' : g ≠ e' := fun h' => hcp' ((he' c hc).mp (h' ▸ hg.2))
        exact huniq g ⟨⟨hgen g hg.1 hg.2 hge hge', hge⟩, hg.2⟩

set_option maxHeartbeats 3200000 in
open Classical in
/-- **Lemma 19 and Corollary 20.** For three nested sets with cuts of size two, the difference
of the largest and the smallest is a burl. -/
theorem ep_nested2_burl {W E : Type*} [Fintype E] (α β : E → W) (L N₁ N₂ N₃ : Finset W)
    (h : EpCubicD α β L) (hb : EpBridgeless α β L) (hconn : EpConnected α β L)
    (h1L : N₁ ⊆ L) (h1ne : N₁ ≠ L) (h21 : N₂ ⊂ N₁) (h32 : N₃ ⊂ N₂) (h3ne : N₃.Nonempty)
    (hd1 : (epCut α β N₁).card = 2) (hd2 : (epCut α β N₂).card = 2)
    (hd3 : (epCut α β N₃).card = 2) : EpBurl α β (N₁ \ N₃) := by
  have h2L : N₂ ⊆ L := h21.1.trans h1L
  have h3L : N₃ ⊆ L := h32.1.trans h2L
  have hnlL : ∀ g, α g ∈ L → α g ≠ β g := by
    intro g hg
    rcases h.1 g with h' | h'
    · exact h'.2.2
    · exact absurd hg h'.1
  have hX₁0 : N₁ \ N₂ ⊆ N₁ \ N₃ := Finset.sdiff_subset_sdiff (Finset.Subset.refl _) h32.1
  have hX₂0 : N₂ \ N₃ ⊆ N₁ \ N₃ := Finset.sdiff_subset_sdiff h21.1 (Finset.Subset.refl _)
  have hX₀L : N₁ \ N₃ ⊆ L := Finset.sdiff_subset.trans h1L
  have hnl0 : ∀ g, α g ∈ N₁ \ N₃ → α g ≠ β g := fun g hg => hnlL g (hX₀L hg)
  have hcompl : ∀ Z : Finset W, epCut α β (L \ Z) = epCut α β Z := by
    intro Z; ext g; rw [mem_epCut, mem_epCut]
    exact epD_cross_compl α β L Z (L \ Z) h (fun w => Finset.mem_sdiff) g
  obtain ⟨z₃, hz₃⟩ := h3ne
  obtain ⟨z₁, hz₁L, hz₁⟩ : ∃ z, z ∈ L ∧ z ∉ N₁ := by
    by_contra hcon
    push_neg at hcon
    exact h1ne (Finset.Subset.antisymm h1L hcon)
  obtain ⟨x₁, hx₁N₁, hx₁N₂⟩ := Finset.exists_of_ssubset h21
  obtain ⟨x₂, hx₂N₂, hx₂N₃⟩ := Finset.exists_of_ssubset h32
  -- cuts of the two layers
  have hge2 : ∀ Z : Finset W, Z ⊆ L → Z.Nonempty → Z ≠ L → 2 ≤ (epCut α β Z).card :=
    fun Z => ep_cut_ge_two α β L hb hconn Z
  have hX₁cut : (epCut α β (N₁ \ N₂)).card = 2 ∨ (epCut α β (N₁ \ N₂)).card = 4 := by
    have c1 := ep_cut_union α β (N₁ \ N₂) N₂ Finset.sdiff_disjoint
    rw [Finset.sdiff_union_of_subset h21.1] at c1
    have c2 := ep_btw_le_cut α β N₂ (N₁ \ N₂) Finset.sdiff_disjoint.symm
    rw [ep_btw_comm] at c2
    have c3 := hge2 (N₁ \ N₂) (Finset.sdiff_subset.trans h1L)
      ⟨x₁, Finset.mem_sdiff.mpr ⟨hx₁N₁, hx₁N₂⟩⟩
      (fun h' => (Finset.mem_sdiff.mp (h' ▸ h3L hz₃ : z₃ ∈ N₁ \ N₂)).2 (h32.1 hz₃))
    omega
  have hX₂cut : (epCut α β (N₂ \ N₃)).card = 2 ∨ (epCut α β (N₂ \ N₃)).card = 4 := by
    have c1 := ep_cut_union α β (N₂ \ N₃) N₃ Finset.sdiff_disjoint
    rw [Finset.sdiff_union_of_subset h32.1] at c1
    have c2 := ep_btw_le_cut α β N₃ (N₂ \ N₃) Finset.sdiff_disjoint.symm
    rw [ep_btw_comm] at c2
    have c3 := hge2 (N₂ \ N₃) (Finset.sdiff_subset.trans h2L)
      ⟨x₂, Finset.mem_sdiff.mpr ⟨hx₂N₂, hx₂N₃⟩⟩
      (fun h' => (Finset.mem_sdiff.mp (h' ▸ h3L hz₃ : z₃ ∈ N₂ \ N₃)).2 hz₃)
    omega
  -- a layer with a cut of size two is a twig
  have htwig : ∀ X : Finset W, X ⊆ N₁ \ N₃ → z₃ ∉ X → (epCut α β X).card = 2 →
      EpBurl α β (N₁ \ N₃) := by
    intro X hX hz hc
    obtain ⟨g, g', hgg', hset⟩ := Finset.card_eq_two.mp hc
    have hcut : ∀ g₀, epCross α β X g₀ ↔ g₀ = g ∨ g₀ = g' := by
      intro g₀; rw [← mem_epCut, hset, Finset.mem_insert, Finset.mem_singleton]
    have := ep_twig2_burl α β L X (L \ X) g g' z₃ h hb (hX.trans hX₀L)
      (fun w => Finset.mem_sdiff) (Finset.mem_sdiff.mpr ⟨h3L hz₃, hz⟩) hgg' hcut
    exact ep_burl_mono α β X (N₁ \ N₃) hX hnl0 this
  rcases hX₁cut with hX₁2 | hX₁4
  · exact htwig _ hX₁0 (fun h' => (Finset.mem_sdiff.mp h').2 (h32.1 hz₃)) hX₁2
  rcases hX₂cut with hX₂2 | hX₂4
  · exact htwig _ hX₂0 (fun h' => (Finset.mem_sdiff.mp h').2 hz₃) hX₂2
  -- no edges between `L \ N₁` and `N₂`, nor between `N₃` and `L \ N₂`
  have hdA : Disjoint (L \ N₁) N₂ := by
    rw [Finset.disjoint_left]; intro w hw hw'
    exact (Finset.mem_sdiff.mp hw).2 (h21.1 hw')
  have hdA' : Disjoint N₃ (L \ N₂) := by
    rw [Finset.disjoint_left]; intro w hw hw'
    exact (Finset.mem_sdiff.mp hw').2 (h32.1 hw)
  have hbtw0 : (epBtw α β (L \ N₁) N₂).card = 0 := by
    have c1 := ep_cut_union α β (L \ N₁) N₂ hdA
    have c2 : L \ (L \ N₁ ∪ N₂) = N₁ \ N₂ := by
      ext w; simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨a1, a2⟩
        refine ⟨?_, fun h' => a2 (Or.inr h')⟩
        by_contra h'; exact a2 (Or.inl ⟨a1, h'⟩)
      · rintro ⟨a1, a2⟩
        exact ⟨h1L a1, fun h' => h'.elim (fun h'' => h''.2 a1) a2⟩
    rw [← hcompl (L \ N₁ ∪ N₂), c2, hcompl N₁] at c1
    omega
  have hbtw0' : (epBtw α β N₃ (L \ N₂)).card = 0 := by
    have c1 := ep_cut_union α β N₃ (L \ N₂) hdA'
    have c2 : L \ (N₃ ∪ L \ N₂) = N₂ \ N₃ := by
      ext w; simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨a1, a2⟩
        refine ⟨?_, fun h' => a2 (Or.inl h')⟩
        by_contra h'; exact a2 (Or.inr ⟨a1, h'⟩)
      · rintro ⟨a1, a2⟩
        exact ⟨h2L a1, fun h' => h'.elim a2 (fun h'' => h''.2 a1)⟩
    rw [← hcompl (N₃ ∪ L \ N₂), c2, hcompl N₂] at c1
    omega
  have hno : ∀ g, ¬(α g ∈ L \ N₁ ∧ β g ∈ N₂) ∧ ¬(α g ∈ N₂ ∧ β g ∈ L \ N₁) := by
    intro g
    have : g ∉ epBtw α β (L \ N₁) N₂ := by
      rw [Finset.card_eq_zero.mp hbtw0]; exact Finset.notMem_empty g
    rw [mem_epBtw] at this
    exact ⟨fun h' => this (Or.inl h'), fun h' => this (Or.inr h')⟩
  have hno' : ∀ g, ¬(α g ∈ N₃ ∧ β g ∈ L \ N₂) ∧ ¬(α g ∈ L \ N₂ ∧ β g ∈ N₃) := by
    intro g
    have : g ∉ epBtw α β N₃ (L \ N₂) := by
      rw [Finset.card_eq_zero.mp hbtw0']; exact Finset.notMem_empty g
    rw [mem_epBtw] at this
    exact ⟨fun h' => this (Or.inl h'), fun h' => this (Or.inr h')⟩
  have hX₀4 : (epCut α β (N₁ \ N₃)).card = 4 := by
    have hd : Disjoint (L \ N₁) N₃ := Finset.disjoint_of_subset_right h32.1 hdA
    have c1 := ep_cut_union α β (L \ N₁) N₃ hd
    have c2 : L \ (L \ N₁ ∪ N₃) = N₁ \ N₃ := by
      ext w; simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨a1, a2⟩
        refine ⟨?_, fun h' => a2 (Or.inr h')⟩
        by_contra h'; exact a2 (Or.inl ⟨a1, h'⟩)
      · rintro ⟨a1, a2⟩
        exact ⟨h1L a1, fun h' => h'.elim (fun h'' => h''.2 a1) a2⟩
    rw [← hcompl (L \ N₁ ∪ N₃), c2, hcompl N₁] at c1
    have c3 := ep_btw_mono α β N₃ N₂ (L \ N₁) h32.1
    rw [ep_btw_comm α β N₃, ep_btw_comm α β N₂] at c3
    omega
  -- the cut edges
  obtain ⟨f, f', hff', hsetf⟩ := Finset.card_eq_two.mp hd1
  obtain ⟨e, e', hee', hsete⟩ := Finset.card_eq_two.mp hd2
  obtain ⟨k, k', hkk', hsetk⟩ := Finset.card_eq_two.mp hd3
  have hcutA : ∀ g, epCross α β (L \ N₁) g ↔ g = f ∨ g = f' := by
    intro g; rw [← mem_epCut, hcompl, hsetf, Finset.mem_insert, Finset.mem_singleton]
  have hcutB : ∀ g, epCross α β N₂ g ↔ g = e ∨ g = e' := by
    intro g; rw [← mem_epCut, hsete, Finset.mem_insert, Finset.mem_singleton]
  have hcutB' : ∀ g, epCross α β (L \ N₂) g ↔ g = e ∨ g = e' := by
    intro g; rw [← mem_epCut, hcompl, hsete, Finset.mem_insert, Finset.mem_singleton]
  have hcutA' : ∀ g, epCross α β N₃ g ↔ g = k ∨ g = k' := by
    intro g; rw [← mem_epCut, hsetk, Finset.mem_insert, Finset.mem_singleton]
  have hsX₁ : (L \ (L \ N₁)) \ N₂ = N₁ \ N₂ := by
    ext w; simp only [Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨a1, a2⟩, a3⟩
      exact ⟨by by_contra h'; exact a2 ⟨a1, h'⟩, a3⟩
    · rintro ⟨a1, a2⟩
      exact ⟨⟨h1L a1, fun h' => h'.2 a1⟩, a2⟩
  have hsX₂ : (L \ N₃) \ (L \ N₂) = N₂ \ N₃ := by
    ext w; simp only [Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨a1, a2⟩, a3⟩
      exact ⟨by by_contra h'; exact a3 ⟨a1, h'⟩, a2⟩
    · rintro ⟨a1, a2⟩
      exact ⟨⟨h2L a1, a2⟩, fun h' => h'.2 a1⟩
  obtain ⟨P, P', hPne, hP, hP'⟩ := ep_sandwich α β L (L \ N₁) N₂ f f' e e' z₁ x₂ h hb
    Finset.sdiff_subset h2L (fun w hw hw' => (Finset.mem_sdiff.mp hw).2 (h21.1 hw'))
    (Finset.mem_sdiff.mpr ⟨hz₁L, hz₁⟩) hx₂N₂ hff' hee' hcutA hcutB hno
  obtain ⟨Q, Q', hQne, hQ, hQ'⟩ := ep_sandwich α β L N₃ (L \ N₂) k k' e e' z₃ x₁ h hb
    h3L Finset.sdiff_subset (fun w hw hw' => (Finset.mem_sdiff.mp hw').2 (h32.1 hw))
    hz₃ (Finset.mem_sdiff.mpr ⟨h1L hx₁N₁, hx₁N₂⟩) hkk' hee' hcutA' hcutB' hno'
  rw [hsX₁] at hP hP'
  rw [hsX₂] at hQ hQ'
  -- the ends of the two middle cut edges
  have hend : ∀ g, (g = e ∨ g = e') →
      epOut α β N₂ g ∈ N₁ \ N₂ ∧ epOut α β (L \ N₂) g ∈ N₂ \ N₃ ∧
      ((α g = epOut α β N₂ g ∧ β g = epOut α β (L \ N₂) g) ∨
        (α g = epOut α β (L \ N₂) g ∧ β g = epOut α β N₂ g)) := by
    intro g hg
    have hcr := (hcutB g).mpr hg
    obtain ⟨hu, x, hx, hends⟩ := epOut_ends α β N₂ g hcr
    have hlive : α g ∈ L ∧ β g ∈ L := by
      rcases h.1 g with h' | h'
      · exact ⟨h'.1, h'.2.1⟩
      · unfold epCross at hcr; rw [h'.2] at hcr; tauto
    have hw : epOut α β (L \ N₂) g = x ∧ epOut α β N₂ g ∈ L := by
      rcases hends with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · refine ⟨?_, e2 ▸ hlive.2⟩
        unfold epOut
        rw [if_neg (fun h' => (Finset.mem_sdiff.mp h').2 (e1 ▸ hx))]
        exact e1
      · refine ⟨?_, e1 ▸ hlive.1⟩
        have : α g ∈ L \ N₂ := Finset.mem_sdiff.mpr ⟨hlive.1, e1 ▸ hu⟩
        rw [show epOut α β (L \ N₂) g = β g from by unfold epOut; rw [if_pos this]]
        exact e2
    rw [hw.1]
    have huN₁ : epOut α β N₂ g ∈ N₁ := by
      by_contra h'
      have hA : epOut α β N₂ g ∈ L \ N₁ := Finset.mem_sdiff.mpr ⟨hw.2, h'⟩
      rcases hends with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact (hno g).2 ⟨e1 ▸ hx, e2 ▸ hA⟩
      · exact (hno g).1 ⟨e1 ▸ hA, e2 ▸ hx⟩
    have hxN₃ : x ∉ N₃ := by
      intro h'
      have hB : epOut α β N₂ g ∈ L \ N₂ := Finset.mem_sdiff.mpr ⟨hw.2, hu⟩
      rcases hends with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact (hno' g).1 ⟨e1 ▸ h', e2 ▸ hB⟩
      · exact (hno' g).2 ⟨e1 ▸ hB, e2 ▸ h'⟩
    refine ⟨Finset.mem_sdiff.mpr ⟨huN₁, hu⟩, Finset.mem_sdiff.mpr ⟨hx, hxN₃⟩, ?_⟩
    rcases hends with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Or.inr ⟨e1, e2⟩
    · exact Or.inl ⟨e1, e2⟩
  have hdX : ∀ w, w ∈ N₁ \ N₂ → w ∉ N₂ \ N₃ := fun w hw hw' =>
    (Finset.mem_sdiff.mp hw).2 (Finset.mem_sdiff.mp hw').1
  -- crossing of singletons by the middle cut edges
  have hcrU : ∀ g, (g = e ∨ g = e') → ∀ c ∈ N₁ \ N₂,
      (epCross α β {c} g ↔ c = epOut α β N₂ g) := by
    intro g hg c hc
    obtain ⟨a1, a2, a3⟩ := hend g hg
    have hne : epOut α β N₂ g ≠ epOut α β (L \ N₂) g := fun h' => hdX _ a1 (h' ▸ a2)
    have hcw : c ≠ epOut α β (L \ N₂) g := fun h' => hdX c hc (h' ▸ a2)
    rw [epCross_singleton]
    rcases a3 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
    · constructor
      · rintro (⟨b1, -⟩ | ⟨-, b2⟩)
        · exact b1.symm
        · exact absurd b2.symm hcw
      · intro h'; exact Or.inl ⟨h'.symm, fun h'' => hcw h''.symm⟩
    · constructor
      · rintro (⟨b1, -⟩ | ⟨-, b2⟩)
        · exact absurd b1.symm hcw
        · exact b2.symm
      · intro h'; exact Or.inr ⟨fun h'' => hcw h''.symm, h'.symm⟩
  have hcrW : ∀ g, (g = e ∨ g = e') → ∀ c ∈ N₂ \ N₃,
      (epCross α β {c} g ↔ c = epOut α β (L \ N₂) g) := by
    intro g hg c hc
    obtain ⟨a1, a2, a3⟩ := hend g hg
    have hcu : c ≠ epOut α β N₂ g := fun h' => hdX _ a1 (h' ▸ hc)
    rw [epCross_singleton]
    rcases a3 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
    · constructor
      · rintro (⟨b1, -⟩ | ⟨-, b2⟩)
        · exact absurd b1.symm hcu
        · exact b2.symm
      · intro h'; exact Or.inr ⟨fun h'' => hcu h''.symm, h'.symm⟩
    · constructor
      · rintro (⟨b1, -⟩ | ⟨-, b2⟩)
        · exact b1.symm
        · exact absurd b2.symm hcu
      · intro h'; exact Or.inl ⟨h'.symm, fun h'' => hcu h''.symm⟩
  have hnotin₁ : ∀ g, (g = e ∨ g = e') → ¬(α g ∈ N₁ \ N₂ ∧ β g ∈ N₁ \ N₂) := by
    intro g hg h'
    obtain ⟨a1, a2, a3⟩ := hend g hg
    rcases a3 with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact hdX _ h'.2 (e2 ▸ a2)
    · exact hdX _ h'.1 (e1 ▸ a2)
  have hnotin₂ : ∀ g, (g = e ∨ g = e') → ¬(α g ∈ N₂ \ N₃ ∧ β g ∈ N₂ \ N₃) := by
    intro g hg h'
    obtain ⟨a1, a2, a3⟩ := hend g hg
    rcases a3 with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact hdX _ (e1 ▸ a1) h'.1
    · exact hdX _ (e2 ▸ a1) h'.2
  have hin0 : ∀ g, (g = e ∨ g = e') → α g ∈ N₁ \ N₃ ∧ β g ∈ N₁ \ N₃ := by
    intro g hg
    obtain ⟨a1, a2, a3⟩ := hend g hg
    rcases a3 with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact ⟨e1 ▸ hX₁0 a1, e2 ▸ hX₂0 a2⟩
    · exact ⟨e1 ▸ hX₂0 a2, e2 ▸ hX₁0 a1⟩
  -- a perfect matching of one layer
  have hlayer : ∀ (X : Finset W) (p p' : W) (S : Finset E), EpSand α β X e p p' S → e ∉ S →
      S ∈ epLM α β X ∧ ∀ g ∈ S, ¬epCross α β X g := by
    intro X p p' S hS heS
    have hin : ∀ g ∈ S, α g ∈ X ∧ β g ∈ X := fun g hg => hS.1 g hg (fun h' => heS (h' ▸ hg))
    refine ⟨⟨fun g hg => Or.inl (hin g hg).1, fun c hc => ?_⟩, fun g hg hcr => ?_⟩
    · rcases hS.2 with ⟨-, hperf⟩ | ⟨h', -⟩
      · obtain ⟨g₀, ⟨⟨g1, g2⟩, g3⟩, huniq⟩ := hperf c hc
        exact ⟨g₀, ⟨g1, g3⟩, fun g hg =>
          huniq g ⟨⟨hg.1, fun h' => heS (h' ▸ hg.1)⟩, hg.2⟩⟩
      · exact absurd h' heS
    · unfold epCross at hcr
      have := hin g hg
      tauto
  by_cases hPP : e ∉ P ∧ e ∉ P'
  · obtain ⟨a1, a2⟩ := hlayer _ _ _ P hP hPP.1
    obtain ⟨b1, b2⟩ := hlayer _ _ _ P' hP' hPP.2
    exact ep_burl_mono α β _ _ hX₁0 hnl0
      (ep_cut4_burl α β L _ h (Finset.sdiff_subset.trans h1L) hX₁4 P P' a1 b1 hPne a2 b2)
  by_cases hQQ : e ∉ Q ∧ e ∉ Q'
  · obtain ⟨a1, a2⟩ := hlayer _ _ _ Q hQ hQQ.1
    obtain ⟨b1, b2⟩ := hlayer _ _ _ Q' hQ' hQQ.2
    exact ep_burl_mono α β _ _ hX₂0 hnl0
      (ep_cut4_burl α β L _ h (Finset.sdiff_subset.trans h2L) hX₂4 Q Q' a1 b1 hQne a2 b2)
  -- gluing
  have hmemG : ∀ (S T : Finset E) (g : E), g ∈ ep2Glue e e' S T ↔
      g ∈ S ∨ g ∈ T ∨ (e ∈ S ∧ g = e') := by
    intro S T g
    unfold ep2Glue
    by_cases heS : e ∈ S
    · rw [if_pos heS, Finset.mem_union, Finset.mem_union, Finset.mem_singleton]; tauto
    · rw [if_neg heS, Finset.mem_union, Finset.mem_union]
      simp only [Finset.notMem_empty]; tauto
  have he'S : ∀ (X : Finset W) (p p' : W) (S : Finset E), EpSand α β X e p p' S →
      ¬(α e' ∈ X ∧ β e' ∈ X) → e' ∉ S := fun X p p' S hS hn h' =>
    hn (hS.1 e' h' (Ne.symm hee'))
  have hglue : ∀ S T : Finset E, EpSand α β (N₁ \ N₂) e (epOut α β N₂ e) (epOut α β N₂ e') S →
      EpSand α β (N₂ \ N₃) e (epOut α β (L \ N₂) e) (epOut α β (L \ N₂) e') T →
      (e ∈ S ↔ e ∈ T) →
      ep2Glue e e' S T ∈ epLM α β (N₁ \ N₃) ∧
        (∀ g ∈ ep2Glue e e' S T, ¬epCross α β (N₁ \ N₃) g) ∧
        (e ∈ ep2Glue e e' S T ↔ e ∈ S) ∧
        (∀ g, g ≠ e → (g ∈ S ↔ g ∈ ep2Glue e e' S T ∧ α g ∈ N₁ \ N₂ ∧ β g ∈ N₁ \ N₂)) ∧
        (∀ g, g ≠ e → (g ∈ T ↔ g ∈ ep2Glue e e' S T ∧ α g ∈ N₂ \ N₃ ∧ β g ∈ N₂ \ N₃)) := by
    intro S T hS hT hiff
    have he'1 := he'S _ _ _ S hS (hnotin₁ e' (Or.inr rfl))
    have he'2 := he'S _ _ _ T hT (hnotin₂ e' (Or.inr rfl))
    have hRe : e ∈ ep2Glue e e' S T ↔ e ∈ S := by
      rw [hmemG]
      constructor
      · rintro (h' | h' | ⟨h', -⟩)
        · exact h'
        · exact hiff.mpr h'
        · exact h'
      · exact fun h' => Or.inl h'
    have hRe' : e' ∈ ep2Glue e e' S T ↔ e ∈ S := by
      rw [hmemG]
      constructor
      · rintro (h' | h' | ⟨h', -⟩)
        · exact absurd h' he'1
        · exact absurd h' he'2
        · exact h'
      · exact fun h' => Or.inr (Or.inr ⟨h', rfl⟩)
    have hinG : ∀ g ∈ ep2Glue e e' S T, α g ∈ N₁ \ N₃ ∧ β g ∈ N₁ \ N₃ := by
      intro g hg
      by_cases hge : g = e
      · exact hin0 g (Or.inl hge)
      · rcases (hmemG S T g).mp hg with h' | h' | ⟨-, h'⟩
        · exact ⟨hX₁0 (hS.1 g h' hge).1, hX₁0 (hS.1 g h' hge).2⟩
        · exact ⟨hX₂0 (hT.1 g h' hge).1, hX₂0 (hT.1 g h' hge).2⟩
        · exact hin0 g (Or.inr h')
    have side₁ : ∀ c ∈ N₁ \ N₂, ∃! g, g ∈ ep2Glue e e' S T ∧ epCross α β {c} g := by
      intro c hc
      refine ep_sand_side α β _ e e' _ _ S _ hS hee' (fun g hg _ => (hmemG S T g).mpr (Or.inl hg))
        (fun g hg hge hge' => ?_) hRe hRe' (hcrU e (Or.inl rfl)) (hcrU e' (Or.inr rfl)) c hc
      rcases (hmemG S T g).mp hg with h' | h' | ⟨-, h'⟩
      · exact Or.inl h'
      · exact Or.inr ⟨fun h'' => hdX _ h'' (hT.1 g h' hge).1,
          fun h'' => hdX _ h'' (hT.1 g h' hge).2⟩
      · exact absurd h' hge'
    have side₂ : ∀ c ∈ N₂ \ N₃, ∃! g, g ∈ ep2Glue e e' S T ∧ epCross α β {c} g := by
      intro c hc
      refine ep_sand_side α β _ e e' _ _ T _ hT hee'
        (fun g hg _ => (hmemG S T g).mpr (Or.inr (Or.inl hg)))
        (fun g hg hge hge' => ?_) (hRe.trans hiff) (hRe'.trans hiff) (hcrW e (Or.inl rfl))
        (hcrW e' (Or.inr rfl)) c hc
      rcases (hmemG S T g).mp hg with h' | h' | ⟨-, h'⟩
      · exact Or.inr ⟨fun h'' => hdX _ (hS.1 g h' hge).1 h'',
          fun h'' => hdX _ (hS.1 g h' hge).2 h''⟩
      · exact Or.inl h'
      · exact absurd h' hge'
    refine ⟨⟨fun g hg => Or.inl (hinG g hg).1, fun c hc => ?_⟩, fun g hg hcr => ?_, hRe,
      fun g hge => ?_, fun g hge => ?_⟩
    · by_cases hc2 : c ∈ N₂
      · exact side₂ c (Finset.mem_sdiff.mpr ⟨hc2, (Finset.mem_sdiff.mp hc).2⟩)
      · exact side₁ c (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hc).1, hc2⟩)
    · unfold epCross at hcr
      have := hinG g hg
      tauto
    · constructor
      · intro hg; exact ⟨(hmemG S T g).mpr (Or.inl hg), hS.1 g hg hge⟩
      · rintro ⟨hg, hin⟩
        rcases (hmemG S T g).mp hg with h' | h' | ⟨-, h'⟩
        · exact h'
        · exact absurd (hT.1 g h' hge).1 (hdX _ hin.1)
        · exact absurd hin (h' ▸ hnotin₁ e' (Or.inr rfl))
    · constructor
      · intro hg; exact ⟨(hmemG S T g).mpr (Or.inr (Or.inl hg)), hT.1 g hg hge⟩
      · rintro ⟨hg, hin⟩
        rcases (hmemG S T g).mp hg with h' | h' | ⟨-, h'⟩
        · exact absurd hin.1 (hdX _ (hS.1 g h' hge).1)
        · exact h'
        · exact absurd hin (h' ▸ hnotin₂ e' (Or.inr rfl))
  -- two compatible pairs with different glued matchings give the burl
  have hfin : ∀ S₁ T₁ S₂ T₂ : Finset E,
      EpSand α β (N₁ \ N₂) e (epOut α β N₂ e) (epOut α β N₂ e') S₁ →
      EpSand α β (N₂ \ N₃) e (epOut α β (L \ N₂) e) (epOut α β (L \ N₂) e') T₁ →
      EpSand α β (N₁ \ N₂) e (epOut α β N₂ e) (epOut α β N₂ e') S₂ →
      EpSand α β (N₂ \ N₃) e (epOut α β (L \ N₂) e) (epOut α β (L \ N₂) e') T₂ →
      (e ∈ S₁ ↔ e ∈ T₁) → (e ∈ S₂ ↔ e ∈ T₂) →
      (((e ∈ S₁ ↔ e ∈ S₂) ∧ (S₁ ≠ S₂ ∨ T₁ ≠ T₂)) ∨ (e ∈ S₁ ∧ e ∉ S₂)) →
      EpBurl α β (N₁ \ N₃) := by
    intro S₁ T₁ S₂ T₂ hS₁ hT₁ hS₂ hT₂ hi₁ hi₂ hdiff
    obtain ⟨a1, a2, a3, a4, a5⟩ := hglue S₁ T₁ hS₁ hT₁ hi₁
    obtain ⟨b1, b2, b3, b4, b5⟩ := hglue S₂ T₂ hS₂ hT₂ hi₂
    refine ep_cut4_burl α β L _ h hX₀L hX₀4 _ _ a1 b1 ?_ a2 b2
    intro heq
    rcases hdiff with ⟨hs, hne | hne⟩ | ⟨hs1, hs2⟩
    · apply hne
      ext g
      by_cases hge : g = e
      · rw [hge]; exact hs
      · rw [a4 g hge, b4 g hge, heq]
    · apply hne
      ext g
      by_cases hge : g = e
      · rw [hge]; exact hi₁.symm.trans (hs.trans hi₂)
      · rw [a5 g hge, b5 g hge, heq]
    · exact hs2 (b3.mp (heq ▸ a3.mpr hs1))
  by_cases p : e ∈ P <;> by_cases p' : e ∈ P' <;> by_cases q : e ∈ Q <;> by_cases q' : e ∈ Q'
  · exact hfin P Q P' Q hP hQ hP' hQ (by tauto) (by tauto) (Or.inl ⟨by tauto, Or.inl hPne⟩)
  · exact hfin P Q P' Q hP hQ hP' hQ (by tauto) (by tauto) (Or.inl ⟨by tauto, Or.inl hPne⟩)
  · exact hfin P Q' P' Q' hP hQ' hP' hQ' (by tauto) (by tauto) (Or.inl ⟨by tauto, Or.inl hPne⟩)
  · exact absurd ⟨q, q'⟩ hQQ
  · exact hfin P Q P Q' hP hQ hP hQ' (by tauto) (by tauto) (Or.inl ⟨by tauto, Or.inr hQne⟩)
  · exact hfin P Q P' Q' hP hQ hP' hQ' (by tauto) (by tauto) (Or.inr ⟨p, p'⟩)
  · exact hfin P Q' P' Q hP hQ' hP' hQ (by tauto) (by tauto) (Or.inr ⟨p, p'⟩)
  · exact absurd ⟨q, q'⟩ hQQ
  · exact hfin P' Q P' Q' hP' hQ hP' hQ' (by tauto) (by tauto) (Or.inl ⟨by tauto, Or.inr hQne⟩)
  · exact hfin P' Q P Q' hP' hQ hP hQ' (by tauto) (by tauto) (Or.inr ⟨p', p⟩)
  · exact hfin P' Q' P Q hP' hQ' hP hQ (by tauto) (by tauto) (Or.inr ⟨p', p⟩)
  · exact absurd ⟨q, q'⟩ hQQ
  · exact absurd ⟨p, p'⟩ hPP
  · exact absurd ⟨p, p'⟩ hPP
  · exact absurd ⟨p, p'⟩ hPP
  · exact absurd ⟨p, p'⟩ hPP

/-- Parity state of the rails: `j ∈ epDelta F k m` iff an odd number of rungs `t ∈ F`, `t < m`,
touch the rail `j` (the rung `t` touches the rails different from `k t`). -/
def epDelta (F : Finset ℕ) (k : ℕ → Fin 3) : ℕ → Finset (Fin 3)
  | 0 => ∅
  | m + 1 => if m ∈ F then symmDiff (epDelta F k m) (Finset.univ.erase (k m)) else epDelta F k m

lemma epDelta_succ_of_notMem (F : Finset ℕ) (k : ℕ → Fin 3) (m : ℕ) (h : m ∉ F) :
    epDelta F k (m + 1) = epDelta F k m := by
  rw [epDelta, if_neg h]

lemma epDelta_succ_of_mem (F : Finset ℕ) (k : ℕ → Fin 3) (m : ℕ) (h : m ∈ F) (j : Fin 3) :
    (j = k m → (j ∈ epDelta F k (m + 1) ↔ j ∈ epDelta F k m)) ∧
      (j ≠ k m → (j ∈ epDelta F k (m + 1) ↔ j ∉ epDelta F k m)) := by
  rw [epDelta, if_pos h, Finset.mem_symmDiff, Finset.mem_erase]
  simp only [Finset.mem_univ, and_true]
  constructor
  · intro hj; tauto
  · intro hj; tauto

lemma epDelta_const (F : Finset ℕ) (k : ℕ → Fin 3) (a b : ℕ) (hab : a ≤ b)
    (h : ∀ t ∈ F, a ≤ t → b ≤ t) : epDelta F k b = epDelta F k a := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hb ih =>
    have hbF : b ∉ F := fun hb' => by have := h b hb' hb; omega
    rw [epDelta_succ_of_notMem F k b hbF]
    exact ih (fun t ht hat => by have := h t ht hat; omega)

lemma epDelta_empty (F : Finset ℕ) (k : ℕ → Fin 3) (m : ℕ) (h : ∀ t ∈ F, m ≤ t) :
    epDelta F k m = ∅ := by
  have := epDelta_const F k 0 m (Nat.zero_le _) (fun t ht _ => h t ht)
  rw [this]; rfl

/-- Along a stretch where the rail `j` is passed, its parity state does not change. -/
lemma epDelta_pass (F : Finset ℕ) (k : ℕ → Fin 3) (j : Fin 3) (a b : ℕ) (hab : a ≤ b)
    (h : ∀ i, a ≤ i → i < b → k i = j) : j ∈ epDelta F k b ↔ j ∈ epDelta F k a := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hb ih =>
    have hk : j = k b := (h b hb (Nat.lt_succ_self b)).symm
    have ih' := ih (fun i hi hib => h i hi (Nat.lt_succ_of_lt hib))
    by_cases hbF : b ∈ F
    · rw [(epDelta_succ_of_mem F k b hbF j).1 hk]; exact ih'
    · rw [epDelta_succ_of_notMem F k b hbF]; exact ih'

/-- An abstract ladder with `n` rungs on the vertex set `X`: three rails, `cut m j` is the
edge of the rail `j` in the `m`-th cut, the rung `m` joins the two vertices `v m j`,
`j ≠ k m`, and the rail `k m` passes the rung `m`. -/
def EpLadder {W E : Type*} (α β : E → W) (X : Finset W) (n : ℕ) (k : ℕ → Fin 3)
    (v : ℕ → Fin 3 → W) (cut : ℕ → Fin 3 → E) (rung : ℕ → E) : Prop :=
  (∀ m < n, cut (m + 1) (k m) = cut m (k m)) ∧
  (∀ m < n, ∀ j, j ≠ k m → ∀ g,
    epCross α β {v m j} g ↔ g = cut m j ∨ g = cut (m + 1) j ∨ g = rung m) ∧
  (∀ m < n, ∀ j, j ≠ k m → cut m j ≠ cut (m + 1) j) ∧
  (∀ m < n, ∀ m' ≤ n, ∀ j, rung m ≠ cut m' j) ∧
  (∀ m < n, ∀ m' < n, rung m = rung m' → m = m') ∧
  (∀ w, w ∈ X ↔ ∃ m < n, ∃ j, j ≠ k m ∧ w = v m j) ∧
  (∀ m < n, ∀ m' < n, ∀ j j', j ≠ k m → j' ≠ k m' → v m j = v m' j' → m = m') ∧
  (∀ m m' j j', m ≤ m' → m' ≤ n → cut m j = cut m' j' →
    j = j' ∧ ∀ i, m ≤ i → i < m' → k i = j) ∧
  (∀ m < n, α (rung m) ∈ X ∧ β (rung m) ∈ X) ∧
  (∀ g, α g ∈ X → α g ≠ β g)

/-- At a vertex with exactly three (distinct) edges, "exactly one edge of `S`" in terms of
membership. -/
lemma ep_exone {W E : Type*} (α β : E → W) (c : W) (a b r : E) (hab : a ≠ b) (har : a ≠ r)
    (hbr : b ≠ r) (hstar : ∀ g, epCross α β {c} g ↔ g = a ∨ g = b ∨ g = r) (S : Finset E) :
    (∃! g, g ∈ S ∧ epCross α β {c} g) ↔
      ((a ∈ S ∧ b ∉ S ∧ r ∉ S) ∨ (a ∉ S ∧ b ∈ S ∧ r ∉ S) ∨ (a ∉ S ∧ b ∉ S ∧ r ∈ S)) := by
  have ca := (hstar a).mpr (Or.inl rfl)
  have cb := (hstar b).mpr (Or.inr (Or.inl rfl))
  have cr := (hstar r).mpr (Or.inr (Or.inr rfl))
  constructor
  · rintro ⟨g₀, ⟨h1, h2⟩, huniq⟩
    have ua : a ∈ S → a = g₀ := fun h' => huniq a ⟨h', ca⟩
    have ub : b ∈ S → b = g₀ := fun h' => huniq b ⟨h', cb⟩
    have ur : r ∈ S → r = g₀ := fun h' => huniq r ⟨h', cr⟩
    rcases (hstar g₀).mp h2 with rfl | rfl | rfl
    · exact Or.inl ⟨h1, fun h' => hab (ub h').symm, fun h' => har (ur h').symm⟩
    · exact Or.inr (Or.inl ⟨fun h' => hab (ua h'), h1, fun h' => hbr (ur h').symm⟩)
    · exact Or.inr (Or.inr ⟨fun h' => har (ua h'), fun h' => hbr (ub h'), h1⟩)
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · refine ⟨a, ⟨h1, ca⟩, fun g hg => ?_⟩
      rcases (hstar g).mp hg.2 with rfl | rfl | rfl
      · rfl
      · exact absurd hg.1 h2
      · exact absurd hg.1 h3
    · refine ⟨b, ⟨h2, cb⟩, fun g hg => ?_⟩
      rcases (hstar g).mp hg.2 with rfl | rfl | rfl
      · exact absurd hg.1 h1
      · rfl
      · exact absurd hg.1 h3
    · refine ⟨r, ⟨h3, cr⟩, fun g hg => ?_⟩
      rcases (hstar g).mp hg.2 with rfl | rfl | rfl
      · exact absurd hg.1 h1
      · exact absurd hg.1 h2
      · rfl

set_option maxHeartbeats 3200000 in
open Classical in
/-- **Flipping a block of rungs.** Let `F` be a set of rungs of `M`, all in `[m₁, m₂)`,
containing every rung of `M` in that range, such that every rail is touched by an even number
of rungs of `F`. Then `M` has a flip set that touches only vertices of the rungs in
`[m₁, m₂)`. -/
theorem ep_ladder_block {W E : Type*} (α β : E → W) (X : Finset W) (n : ℕ)
    (k : ℕ → Fin 3) (v : ℕ → Fin 3 → W) (cut : ℕ → Fin 3 → E) (rung : ℕ → E)
    (hl : EpLadder α β X n k v cut rung) (M : Finset E) (hM : M ∈ epLM α β X)
    (F : Finset ℕ) (m₁ m₂ : ℕ) (hm₂ : m₂ ≤ n)
    (hF : ∀ t ∈ F, m₁ ≤ t ∧ t < m₂ ∧ rung t ∈ M) (hne : F.Nonempty)
    (hall : ∀ m, m₁ ≤ m → m < m₂ → rung m ∈ M → m ∈ F) (hzero : epDelta F k m₂ = ∅) :
    ∃ D : Finset E, D.Nonempty ∧ (∀ e ∈ D, α e ∈ X ∧ β e ∈ X) ∧ symmDiff M D ∈ epLM α β X ∧
      ∀ c, epTouch α β D c → ∃ m j, m₁ ≤ m ∧ m < m₂ ∧ j ≠ k m ∧ c = v m j := by
  obtain ⟨hpass, hstar, hne1, hrc, hrinj, hmem, hvinj, hcuteq, hrin, -⟩ := hl
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : ℕ → Finset (Fin 3), Δ = epDelta F k := ⟨_, rfl⟩
  have hFn : ∀ t ∈ F, t < n := fun t ht => lt_of_lt_of_le (hF t ht).2.1 hm₂
  -- basic facts on the parity states
  have hd1 : ∀ m, m ∉ F → Δ (m + 1) = Δ m := fun m hm => by
    rw [hΔ]; exact epDelta_succ_of_notMem F k m hm
  have hd2 : ∀ m, m ∈ F → ∀ j, (j = k m → (j ∈ Δ (m + 1) ↔ j ∈ Δ m)) ∧
      (j ≠ k m → (j ∈ Δ (m + 1) ↔ j ∉ Δ m)) := fun m hm j => by
    rw [hΔ]; exact epDelta_succ_of_mem F k m hm j
  have hlow : ∀ m, m ≤ m₁ → Δ m = ∅ := fun m hm => by
    rw [hΔ]; exact epDelta_empty F k m (fun t ht => hm.trans (hF t ht).1)
  have hhigh : ∀ m, m₂ ≤ m → Δ m = ∅ := fun m hm => by
    rw [hΔ, epDelta_const F k m₂ m hm (fun t ht h' => by have := (hF t ht).2.1; omega)]
    exact hzero
  have hrange : ∀ m, (Δ m).Nonempty → m₁ < m ∧ m < m₂ := by
    intro m hm
    constructor
    · by_contra h'
      rw [hlow m (by omega)] at hm; exact Finset.not_nonempty_empty hm
    · by_contra h'
      rw [hhigh m (by omega)] at hm; exact Finset.not_nonempty_empty hm
  have hpassΔ : ∀ j a b, a ≤ b → (∀ i, a ≤ i → i < b → k i = j) → (j ∈ Δ b ↔ j ∈ Δ a) :=
    fun j a b hab h' => by rw [hΔ]; exact epDelta_pass F k j a b hab h'
  have hsame : ∀ m, m < n → ∀ j, j = k m → (j ∈ Δ (m + 1) ↔ j ∈ Δ m) := by
    intro m hm j hj
    by_cases hmF : m ∈ F
    · exact (hd2 m hmF j).1 hj
    · rw [hd1 m hmF]
  -- the flip set
  obtain ⟨D, hD⟩ : ∃ D : Finset E, D = F.image rung ∪
      ((Finset.range (n + 1) ×ˢ (Finset.univ : Finset (Fin 3))).filter
        (fun x => x.2 ∈ Δ x.1)).image (fun x => cut x.1 x.2) := ⟨_, rfl⟩
  have hDmem : ∀ g, g ∈ D ↔ (∃ t ∈ F, rung t = g) ∨ ∃ m j, m ≤ n ∧ j ∈ Δ m ∧ cut m j = g := by
    intro g
    rw [hD, Finset.mem_union, Finset.mem_image, Finset.mem_image]
    constructor
    · rintro (h' | ⟨x, hx, hxg⟩)
      · exact Or.inl h'
      · rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hx
        exact Or.inr ⟨x.1, x.2, by omega, hx.2, hxg⟩
    · rintro (h' | ⟨m, j, hm, hj, hg⟩)
      · exact Or.inl h'
      · exact Or.inr ⟨(m, j), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨Finset.mem_range.mpr (by omega), Finset.mem_univ _⟩, hj⟩, hg⟩
  have hW1 : ∀ m, m ≤ n → ∀ j, (cut m j ∈ D ↔ j ∈ Δ m) := by
    intro m hm j
    rw [hDmem]
    constructor
    · rintro (⟨t, ht, htg⟩ | ⟨m', j', hm', hj', hg⟩)
      · exact absurd htg (hrc t (hFn t ht) m hm j)
      · rcases le_total m m' with hle | hle
        · obtain ⟨e1, e2⟩ := hcuteq m m' j j' hle hm' hg.symm
          rw [← hpassΔ j m m' hle e2, e1]; exact hj'
        · obtain ⟨e1, e2⟩ := hcuteq m' m j' j hle hm hg
          rw [← e1, hpassΔ j' m' m hle e2]; exact hj'
    · intro hj; exact Or.inr ⟨m, j, hm, hj, rfl⟩
  have hW2 : ∀ m, m < n → (rung m ∈ D ↔ m ∈ F) := by
    intro m hm
    rw [hDmem]
    constructor
    · rintro (⟨t, ht, htg⟩ | ⟨m', j', hm', -, hg⟩)
      · rw [← hrinj t (hFn t ht) m hm htg]; exact ht
      · exact absurd hg.symm (hrc m hm m' hm' j')
    · intro hmF; exact Or.inl ⟨m, hmF, rfl⟩
  -- the three edges at a vertex of the ladder, before and after the flip
  have hvert : ∀ m, m < n → ∀ j, j ≠ k m →
      ∃! g, g ∈ symmDiff M D ∧ epCross α β {v m j} g := by
    intro m hm j hj
    have hab := hne1 m hm j hj
    have har : cut m j ≠ rung m := fun h' => hrc m hm m (by omega) j h'.symm
    have hbr : cut (m + 1) j ≠ rung m := fun h' => hrc m hm (m + 1) (by omega) j h'.symm
    have hX : v m j ∈ X := (hmem _).mpr ⟨m, hm, j, hj, rfl⟩
    have h0 := (ep_exone α β (v m j) _ _ _ hab har hbr (hstar m hm j hj) M).mp (hM.2 _ hX)
    rw [ep_exone α β (v m j) _ _ _ hab har hbr (hstar m hm j hj)]
    simp only [Finset.mem_symmDiff, hW1 m (by omega) j, hW1 (m + 1) (by omega) j, hW2 m hm]
    by_cases hmF : m ∈ F
    · have hr := (hF m hmF).2.2
      have hflip := (hd2 m hmF j).2 hj
      by_cases hA : j ∈ Δ m
      · have hB : j ∉ Δ (m + 1) := fun h' => (hflip.mp h') hA
        tauto
      · have hB : j ∈ Δ (m + 1) := hflip.mpr hA
        tauto
    · rw [hd1 m hmF]
      by_cases hA : j ∈ Δ m
      · have hr : rung m ∉ M := by
          intro hr
          obtain ⟨a1, a2⟩ := hrange m ⟨j, hA⟩
          exact hmF (hall m (by omega) a2 hr)
        tauto
      · tauto
  -- both ends of the edges of the flip set are in the ladder
  have hP1 : ∀ m, m ≤ n → ∀ j, j ∈ Δ m → ∃ m', m' < m ∧ j ≠ k m' ∧ cut m j = cut (m' + 1) j := by
    intro m
    induction m with
    | zero =>
      intro _ j hj
      rw [hlow 0 (Nat.zero_le _)] at hj
      exact absurd hj (Finset.notMem_empty j)
    | succ m ih =>
      intro hm j hj
      by_cases hjk : j = k m
      · have hj' := (hsame m (by omega) j hjk).mp hj
        obtain ⟨m', a1, a2, a3⟩ := ih (by omega) j hj'
        refine ⟨m', by omega, a2, ?_⟩
        rw [← a3, hjk]; exact hpass m (by omega)
      · exact ⟨m, Nat.lt_succ_self m, hjk, rfl⟩
  have hP2 : ∀ d m, m + d = n → ∀ j, j ∈ Δ m →
      ∃ m', m ≤ m' ∧ m' < n ∧ j ≠ k m' ∧ cut m j = cut m' j := by
    intro d
    induction d with
    | zero =>
      intro m hm j hj
      rw [hhigh m (by omega)] at hj
      exact absurd hj (Finset.notMem_empty j)
    | succ d ih =>
      intro m hm j hj
      by_cases hjk : j = k m
      · have hj' := (hsame m (by omega) j hjk).mpr hj
        obtain ⟨m', a1, a2, a3, a4⟩ := ih (m + 1) (by omega) j hj'
        refine ⟨m', by omega, a2, a3, ?_⟩
        rw [← a4, hjk]; exact (hpass m (by omega)).symm
      · exact ⟨m, le_refl m, by omega, hjk, rfl⟩
  have hDin : ∀ e ∈ D, α e ∈ X ∧ β e ∈ X := by
    intro e he
    rcases (hDmem e).mp he with ⟨t, ht, rfl⟩ | ⟨m, j, hm, hj, rfl⟩
    · exact hrin t (hFn t ht)
    · obtain ⟨m', a1, a2, a3⟩ := hP1 m hm j hj
      obtain ⟨m'', b1, b2, b3, b4⟩ := hP2 (n - m) m (by omega) j hj
      have c1 : epCross α β {v m' j} (cut m j) :=
        (hstar m' (by omega) j a2 _).mpr (Or.inr (Or.inl a3))
      have c2 : epCross α β {v m'' j} (cut m j) :=
        (hstar m'' b2 j b3 _).mpr (Or.inl b4)
      have hne' : v m' j ≠ v m'' j := fun h' => by
        have := hvinj m' (by omega) m'' b2 j j a2 b3 h'; omega
      have hX1 : v m' j ∈ X := (hmem _).mpr ⟨m', by omega, j, a2, rfl⟩
      have hX2 : v m'' j ∈ X := (hmem _).mpr ⟨m'', b2, j, b3, rfl⟩
      rw [epCross_singleton] at c1 c2
      rcases c1 with ⟨d1, d2⟩ | ⟨d1, d2⟩ <;> rcases c2 with ⟨d3, d4⟩ | ⟨d3, d4⟩
      · exact absurd (d1.symm.trans d3) hne'
      · exact ⟨d1 ▸ hX1, d4 ▸ hX2⟩
      · exact ⟨d3 ▸ hX2, d2 ▸ hX1⟩
      · exact absurd (d2.symm.trans d4) hne'
  refine ⟨D, ?_, hDin, ⟨fun e he => ?_, fun c hc => ?_⟩, fun c hc => ?_⟩
  · obtain ⟨t, ht⟩ := hne
    exact ⟨rung t, (hW2 t (hFn t ht)).mpr ht⟩
  · rcases Finset.mem_symmDiff.mp he with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hM.1 e h1
    · exact Or.inl (hDin e h1).1
  · obtain ⟨m, hm, j, hj, rfl⟩ := (hmem c).mp hc
    exact hvert m hm j hj
  · obtain ⟨e, he, hcr⟩ := hc
    have hcX : c ∈ X := by
      rw [epCross_singleton] at hcr
      rcases hcr with ⟨d1, -⟩ | ⟨-, d1⟩
      · exact d1 ▸ (hDin e he).1
      · exact d1 ▸ (hDin e he).2
    obtain ⟨m, hm, j, hj, rfl⟩ := (hmem c).mp hcX
    refine ⟨m, j, ?_, ?_, hj, rfl⟩
    · rcases (hstar m hm j hj e).mp hcr with rfl | rfl | rfl
      · have := hrange m ⟨j, (hW1 m (by omega) j).mp he⟩; omega
      · have := hrange (m + 1) ⟨j, (hW1 (m + 1) (by omega) j).mp he⟩; omega
      · exact (hF m ((hW2 m hm).mp he)).1
    · rcases (hstar m hm j hj e).mp hcr with rfl | rfl | rfl
      · have := hrange m ⟨j, (hW1 m (by omega) j).mp he⟩; omega
      · have := hrange (m + 1) ⟨j, (hW1 (m + 1) (by omega) j).mp he⟩; omega
      · exact (hF m ((hW2 m hm).mp he)).2.1

lemma ep_fin3_parity : ∀ (A : Finset (Fin 3)) (j : Fin 3),
    (symmDiff A (Finset.univ.erase j)).card % 2 = A.card % 2 := by decide

lemma ep_fin3_evens :
    (Finset.univ.filter (fun A : Finset (Fin 3) => A.card % 2 = 0)).card = 4 := by decide

lemma epDelta_succ_mem_eq (F : Finset ℕ) (k : ℕ → Fin 3) (m : ℕ) (h : m ∈ F) :
    epDelta F k (m + 1) = symmDiff (epDelta F k m) (Finset.univ.erase (k m)) := by
  rw [epDelta, if_pos h]

lemma epDelta_even (F : Finset ℕ) (k : ℕ → Fin 3) (m : ℕ) : (epDelta F k m).card % 2 = 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    by_cases h : m ∈ F
    · rw [epDelta_succ_mem_eq F k m h, ep_fin3_parity]; exact ih
    · rw [epDelta_succ_of_notMem F k m h]; exact ih

set_option maxHeartbeats 1600000 in
open Classical in
/-- **Pigeonhole lemma for ladders.** If `M` contains four rungs among the rungs `lo, …, hi`,
then `M` has a flip set touching only vertices of these rungs. -/
theorem ep_ladder_flip {W E : Type*} (α β : E → W) (X : Finset W) (n : ℕ)
    (k : ℕ → Fin 3) (v : ℕ → Fin 3 → W) (cut : ℕ → Fin 3 → E) (rung : ℕ → E)
    (hl : EpLadder α β X n k v cut rung) (M : Finset E) (hM : M ∈ epLM α β X)
    (lo hi : ℕ) (hhi : hi < n)
    (h4 : 4 ≤ ((Finset.Icc lo hi).filter (fun m => rung m ∈ M)).card) :
    ∃ D : Finset E, D.Nonempty ∧ (∀ e ∈ D, α e ∈ X ∧ β e ∈ X) ∧ symmDiff M D ∈ epLM α β X ∧
      ∀ c, epTouch α β D c → ∃ m j, lo ≤ m ∧ m ≤ hi ∧ j ≠ k m ∧ c = v m j := by
  obtain ⟨F₀, hF₀⟩ : ∃ F₀ : Finset ℕ, F₀ = (Finset.Icc lo hi).filter (fun m => rung m ∈ M) :=
    ⟨_, rfl⟩
  rw [← hF₀] at h4
  have hF₀mem : ∀ m, m ∈ F₀ ↔ (lo ≤ m ∧ m ≤ hi) ∧ rung m ∈ M := by
    intro m; rw [hF₀, Finset.mem_filter, Finset.mem_Icc]
  -- five stages, four possible parity states
  have hcardS : 4 < (insert lo (F₀.image (fun t => t + 1))).card := by
    rw [Finset.card_insert_of_notMem, Finset.card_image_of_injective _ (fun a b h => by
      simpa using h)]
    · omega
    · intro h'
      obtain ⟨t, ht, hte⟩ := Finset.mem_image.mp h'
      have := ((hF₀mem t).mp ht).1.1
      omega
  rw [← ep_fin3_evens] at hcardS
  obtain ⟨x, hx, y, hy, hxy, hPi⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcardS
    (f := epDelta F₀ k) (fun m _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, epDelta_even F₀ k m⟩)
  have hSlo : ∀ z ∈ insert lo (F₀.image (fun t => t + 1)), lo ≤ z := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact le_refl _
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
      have := ((hF₀mem t).mp ht).1.1
      omega
  have main : ∀ x y, x ∈ insert lo (F₀.image (fun t => t + 1)) →
      y ∈ insert lo (F₀.image (fun t => t + 1)) → x < y → epDelta F₀ k x = epDelta F₀ k y →
      ∃ D : Finset E, D.Nonempty ∧ (∀ e ∈ D, α e ∈ X ∧ β e ∈ X) ∧
        symmDiff M D ∈ epLM α β X ∧
        ∀ c, epTouch α β D c → ∃ m j, lo ≤ m ∧ m ≤ hi ∧ j ≠ k m ∧ c = v m j := by
    intro x y hx hy hlt hPi
    have hxlo := hSlo x hx
    obtain ⟨t, ht, hty⟩ : ∃ t ∈ F₀, t + 1 = y := by
      rcases Finset.mem_insert.mp hy with h' | h'
      · omega
      · exact Finset.mem_image.mp h'
    obtain ⟨⟨ht1, ht2⟩, ht3⟩ := (hF₀mem t).mp ht
    have hmemF : ∀ m, m ∈ (Finset.Ico x y).filter (fun m => rung m ∈ M) ↔
        (x ≤ m ∧ m < y) ∧ rung m ∈ M := by
      intro m; rw [Finset.mem_filter, Finset.mem_Ico]
    -- relation between the parity states of the block and of all rungs
    have hrel : ∀ m, x ≤ m → m ≤ y →
        epDelta ((Finset.Ico x y).filter (fun m => rung m ∈ M)) k m =
          symmDiff (epDelta F₀ k m) (epDelta F₀ k x) := by
      intro m hxm
      induction m, hxm using Nat.le_induction with
      | base =>
        intro _
        rw [symmDiff_self]
        exact epDelta_empty _ k x (fun t ht => ((hmemF t).mp ht).1.1)
      | succ m hm ih =>
        intro hmy
        have ih' := ih (by omega)
        by_cases hs : rung m ∈ M
        · have h1 : m ∈ (Finset.Ico x y).filter (fun m => rung m ∈ M) :=
            (hmemF m).mpr ⟨⟨hm, by omega⟩, hs⟩
          have h2 : m ∈ F₀ := (hF₀mem m).mpr ⟨⟨by omega, by omega⟩, hs⟩
          rw [epDelta_succ_mem_eq _ k m h1, epDelta_succ_mem_eq _ k m h2, ih']
          exact symmDiff_right_comm _ _ _
        · have h1 : m ∉ (Finset.Ico x y).filter (fun m => rung m ∈ M) :=
            fun h' => hs ((hmemF m).mp h').2
          have h2 : m ∉ F₀ := fun h' => hs ((hF₀mem m).mp h').2
          rw [epDelta_succ_of_notMem _ k m h1, epDelta_succ_of_notMem _ k m h2, ih']
    have hzero : epDelta ((Finset.Ico x y).filter (fun m => rung m ∈ M)) k y = ∅ := by
      rw [hrel y (le_of_lt hlt) (le_refl y), hPi, symmDiff_self]; rfl
    obtain ⟨D, d1, d2, d3, d4⟩ := ep_ladder_block α β X n k v cut rung hl M hM
      ((Finset.Ico x y).filter (fun m => rung m ∈ M)) x y (by omega)
      (fun m hm => ⟨((hmemF m).mp hm).1.1, ((hmemF m).mp hm).1.2, ((hmemF m).mp hm).2⟩)
      ⟨t, (hmemF t).mpr ⟨⟨by omega, by omega⟩, ht3⟩⟩
      (fun m h1 h2 h3 => (hmemF m).mpr ⟨⟨h1, h2⟩, h3⟩) hzero
    refine ⟨D, d1, d2, d3, fun c hc => ?_⟩
    obtain ⟨m, j, a1, a2, a3, a4⟩ := d4 c hc
    exact ⟨m, j, by omega, by omega, a3, a4⟩
  rcases Nat.lt_or_gt_of_ne hxy with hlt | hlt
  · exact main x y hx hy hlt hPi
  · exact main y x hy hx hlt hPi.symm

set_option maxHeartbeats 1600000 in
open Classical in
/-- A local matching of a ladder containing `R` rungs has `R / 4` disjoint flip sets. -/
theorem ep_ladder_alt {W E : Type*} (α β : E → W) (X : Finset W) (n : ℕ)
    (k : ℕ → Fin 3) (v : ℕ → Fin 3 → W) (cut : ℕ → Fin 3 → E) (rung : ℕ → E)
    (hl : EpLadder α β X n k v cut rung) (M : Finset E) (hM : M ∈ epLM α β X) :
    EpAlt α β X M (((Finset.range n).filter (fun m => rung m ∈ M)).card / 4) := by
  obtain ⟨T, hT⟩ : ∃ T : Finset ℕ, T = (Finset.range n).filter (fun m => rung m ∈ M) :=
    ⟨_, rfl⟩
  rw [← hT]
  have hTmem : ∀ m, m ∈ T ↔ m < n ∧ rung m ∈ M := by
    intro m; rw [hT, Finset.mem_filter, Finset.mem_range]
  have hidx : ∀ (g : Fin (T.card / 4)) (i : Fin 4), 4 * g.1 + i.1 < T.card := by
    intro g i
    have := g.2
    have := i.2
    omega
  obtain ⟨f, hf⟩ : ∃ f : Fin (T.card / 4) → Fin 4 → ℕ,
      ∀ g i, f g i = T.orderEmbOfFin rfl ⟨4 * g.1 + i.1, hidx g i⟩ := ⟨_, fun _ _ => rfl⟩
  have hfT : ∀ g i, f g i ∈ T := fun g i => by rw [hf]; exact Finset.orderEmbOfFin_mem T rfl _
  have hflt : ∀ g i g' i', 4 * g.1 + i.1 < 4 * g'.1 + i'.1 → f g i < f g' i' := by
    intro g i g' i' hlt
    rw [hf, hf]
    exact (T.orderEmbOfFin rfl).strictMono (by rw [Fin.lt_def]; exact hlt)
  have hfle : ∀ g i i', i.1 ≤ i'.1 → f g i ≤ f g i' := by
    intro g i i' hle
    rcases Nat.lt_or_ge i.1 i'.1 with h' | h'
    · exact le_of_lt (hflt g i g i' (by omega))
    · have : i = i' := Fin.ext (by omega)
      rw [this]
  have hfour : ∀ g : Fin (T.card / 4),
      4 ≤ ((Finset.Icc (f g 0) (f g 3)).filter (fun m => rung m ∈ M)).card := by
    intro g
    have hinj : Function.Injective (f g) := by
      intro i i' h'
      by_contra hne
      rcases Nat.lt_or_gt_of_ne (fun h'' => hne (Fin.ext h'')) with hlt | hlt
      · have := hflt g i g i' (by omega); omega
      · have := hflt g i' g i (by omega); omega
    have hsub : (Finset.univ : Finset (Fin 4)).image (f g) ⊆
        (Finset.Icc (f g 0) (f g 3)).filter (fun m => rung m ∈ M) := by
      intro m hm
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hm
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hfle g 0 i (Nat.zero_le _), hfle g i 3 (by have := i.2; simp; omega)⟩,
        ((hTmem _).mp (hfT g i)).2⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hinj] at this
    simpa using this
  have hex : ∀ g : Fin (T.card / 4), ∃ D : Finset E, D.Nonempty ∧
      (∀ e ∈ D, α e ∈ X ∧ β e ∈ X) ∧ symmDiff M D ∈ epLM α β X ∧
      ∀ c, epTouch α β D c → ∃ m j, f g 0 ≤ m ∧ m ≤ f g 3 ∧ j ≠ k m ∧ c = v m j :=
    fun g => ep_ladder_flip α β X n k v cut rung hl M hM (f g 0) (f g 3)
      ((hTmem _).mp (hfT g 3)).1 (hfour g)
  choose D hD1 hD2 hD3 hD4 using hex
  refine ⟨D, hD1, hD2, hD3, fun g g' hgg' c hc => ?_⟩
  obtain ⟨m, j, a1, a2, a3, a4⟩ := hD4 g c hc.1
  obtain ⟨m', j', b1, b2, b3, b4⟩ := hD4 g' c hc.2
  have hn3 : ∀ g, f g 3 < n := fun g => ((hTmem _).mp (hfT g 3)).1
  have hmm : m = m' := hl.2.2.2.2.2.2.1 m (lt_of_le_of_lt a2 (hn3 g)) m'
    (lt_of_le_of_lt b2 (hn3 g')) j j' a3 b3 (a4.symm.trans b4)
  rcases Nat.lt_or_gt_of_ne (fun h' => hgg' (Fin.ext h')) with hlt | hlt
  · have := hflt g 3 g' 0 (by simp; omega); omega
  · have := hflt g' 3 g 0 (by simp; omega); omega

set_option maxHeartbeats 1600000 in
open Classical in
/-- **Ladders with thirteen rungs are burls.** -/
theorem ep_ladder_burl {W E : Type*} [Fintype E] (α β : E → W) (X : Finset W) (n : ℕ)
    (k : ℕ → Fin 3) (v : ℕ → Fin 3 → W) (cut : ℕ → Fin 3 → E) (rung : ℕ → E)
    (hl : EpLadder α β X n k v cut rung) (hn : 13 ≤ n) : EpBurl α β X := by
  intro p hp
  obtain ⟨hp0, hpLM, hp1, hpbal⟩ := hp
  have hnl := hl.2.2.2.2.2.2.2.2.2
  have hrin := hl.2.2.2.2.2.2.2.2.1
  have hR : ∀ N : Finset E, (((Finset.range n).filter (fun m => rung m ∈ N)).card : ℝ) =
      ∑ m ∈ Finset.range n, epInd N (rung m) := by
    intro N
    rw [Finset.card_filter]
    push_cast
    rfl
  have hterm : ∀ N : Finset E, p N * ((∑ m ∈ Finset.range n, epInd N (rung m)) - 3) / 4 ≤
      p N * (epAltNum α β X N : ℝ) := by
    intro N
    by_cases hpN : p N = 0
    · rw [hpN]; simp
    · have h1 := epAlt_le_altNum' α β X hnl N _
        (ep_ladder_alt α β X n k v cut rung hl N (hpLM N hpN))
      have h2 : (((Finset.range n).filter (fun m => rung m ∈ N)).card : ℝ) - 3 ≤
          4 * (epAltNum α β X N : ℝ) := by
        have : ((Finset.range n).filter (fun m => rung m ∈ N)).card ≤
            4 * epAltNum α β X N + 3 := by omega
        have h3 : (((Finset.range n).filter (fun m => rung m ∈ N)).card : ℝ) ≤
            4 * (epAltNum α β X N : ℝ) + 3 := by exact_mod_cast this
        linarith
      rw [← hR N, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (by linarith) (hp0 N)
  have hsum : ∑ N, p N * (∑ m ∈ Finset.range n, epInd N (rung m)) = (n : ℝ) / 3 := by
    have : ∀ N, p N * (∑ m ∈ Finset.range n, epInd N (rung m)) =
        ∑ m ∈ Finset.range n, p N * epInd N (rung m) := fun N => Finset.mul_sum _ _ _
    rw [Finset.sum_congr rfl (fun N _ => this N), Finset.sum_comm]
    have h3 : ∀ m ∈ Finset.range n, ∑ N, p N * epInd N (rung m) = 1 / 3 := fun m hm =>
      hpbal (rung m) (Or.inl (hrin m (Finset.mem_range.mp hm)).1)
    rw [Finset.sum_congr rfl h3, Finset.sum_const, Finset.card_range]
    simp; ring
  have htot : ∑ N, p N * ((∑ m ∈ Finset.range n, epInd N (rung m)) - 3) / 4 =
      ((n : ℝ) / 3 - 3) / 4 := by
    have : ∀ N, p N * ((∑ m ∈ Finset.range n, epInd N (rung m)) - 3) / 4 =
        (p N * (∑ m ∈ Finset.range n, epInd N (rung m)) - 3 * p N) / 4 := fun N => by ring
    rw [Finset.sum_congr rfl (fun N _ => this N), ← Finset.sum_div, Finset.sum_sub_distrib,
      hsum, ← Finset.mul_sum, hp1]
    ring
  have hn' : (13 : ℝ) ≤ n := by exact_mod_cast hn
  calc (1 : ℝ) / 3 ≤ ((n : ℝ) / 3 - 3) / 4 := by linarith
    _ = ∑ N, p N * ((∑ m ∈ Finset.range n, epInd N (rung m)) - 3) / 4 := htot.symm
    _ ≤ ∑ N, p N * (epAltNum α β X N : ℝ) := Finset.sum_le_sum (fun N _ => hterm N)

lemma ep_btw_union_le {W E : Type*} [Fintype E] [DecidableEq W] (α β : E → W)
    (P Q R : Finset W) :
    (epBtw α β P (Q ∪ R)).card ≤ (epBtw α β P Q).card + (epBtw α β P R).card := by
  classical
  refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro g hg
  rw [mem_epBtw] at hg
  rw [Finset.mem_union, mem_epBtw, mem_epBtw]
  simp only [Finset.mem_union] at hg
  tauto

/-- An edge cannot join `R` to two disjoint sets that are both disjoint from `R`. -/
lemma ep_btw_disj {W E : Type*} [Fintype E] (α β : E → W) (R P Q : Finset W) (g : E)
    (h1 : g ∈ epBtw α β R P) (h2 : g ∈ epBtw α β R Q) (hRP : Disjoint R P)
    (hRQ : Disjoint R Q) (hPQ : Disjoint P Q) : False := by
  rw [mem_epBtw] at h1 h2
  rcases h1 with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases h2 with ⟨b1, b2⟩ | ⟨b1, b2⟩
  · exact Finset.disjoint_left.mp hPQ a2 b2
  · exact Finset.disjoint_left.mp hRQ a1 b1
  · exact Finset.disjoint_left.mp hRP b1 a1
  · exact Finset.disjoint_left.mp hPQ a1 b1

lemma ep_three_mem {E : Type*} [DecidableEq E] (S : Finset E) (hS : S.card = 3) (a b c : E)
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (g : E) :
    g ∈ S ↔ g = a ∨ g = b ∨ g = c := by
  have hsub : ({a, b, c} : Finset E) ⊆ S := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl <;> assumption
  have hcard : ({a, b, c} : Finset E).card = 3 :=
    Finset.card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩
  have := Finset.eq_of_subset_of_card_le hsub (by omega)
  rw [← this]
  simp only [Finset.mem_insert, Finset.mem_singleton]

open Classical in
/-- In a decomposition refining `𝒴`, the atom of a member that has a child is not in `𝒴`. -/
lemma ep_atom_notMem_refined {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (r : W)
    (𝒮 𝒴 : Finset (Finset W)) (hdec : EpDecomp α β L r 𝒮) (href : EpRefines L r 𝒮 𝒴)
    (N C : Finset W) (hN : N ∈ 𝒮) (hC : C ∈ epChildren 𝒮 N) (hne : (epAtom 𝒮 N).Nonempty) :
    epAtom 𝒮 N ∉ 𝒴 := by
  intro hY
  obtain ⟨hCS, hCN, -⟩ := (mem_epChildren 𝒮 N C).mp hC
  obtain ⟨c, hc⟩ := (hdec.2.1 C hCS).2.1
  have hsub : epAtom 𝒮 N ⊆ N := fun w hw => ((mem_epAtom 𝒮 N w).mp hw).1
  rcases href _ hY with ⟨h1, -⟩ | ⟨h1, -, -⟩
  · have hss : epAtom 𝒮 N ⊂ N := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun he => ?_⟩
      have : c ∈ epAtom 𝒮 N := by rw [he]; exact hCN.1 hc
      exact ((mem_epAtom 𝒮 N c).mp this).2 C hCS hCN hc
    obtain ⟨w, hw⟩ := hne
    exact ((mem_epAtom 𝒮 N w).mp hw).2 _ h1 hss hw
  · exact (hdec.2.1 N hN).2.2.1 (hsub h1)

set_option maxHeartbeats 3200000 in
open Classical in
/-- **A rung node.** In a `𝒴`-maximum decomposition of a multigraph without a core, a member
`N` with a single child `C`, both with cuts of size three, has an atom `{x, y}` forming a rung:
`x ~ y`, each of `x`, `y` has one edge leaving `N` and one edge into `C`, and one edge joins
the outside of `N` to `C`. -/
theorem ep_rung_node {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (r : W)
    (𝒮 𝒴 : Finset (Finset W)) (h : EpCubicD α β L) (hb : EpBridgeless α β L)
    (hconn : EpConnected α β L) (hr : r ∈ L) (hdec : EpDecomp α β L r 𝒮)
    (href : EpRefines L r 𝒮 𝒴)
    (hmax : ∀ 𝒮', EpDecomp α β L r 𝒮' → EpRefines L r 𝒮' 𝒴 → 𝒮'.card ≤ 𝒮.card)
    (hnc : ¬EpHasCore α β L) (N C : Finset W) (hN : N ∈ 𝒮) (hch : epChildren 𝒮 N = {C})
    (hdN : (epCut α β N).card = 3) (hdC : (epCut α β C).card = 3) :
    ∃ (x y : W) (rg ix iy ox oy ps : E), x ≠ y ∧ N \ C = {x, y} ∧
      (∀ g, epCross α β {x} g ↔ g = ix ∨ g = ox ∨ g = rg) ∧
      (∀ g, epCross α β {y} g ↔ g = iy ∨ g = oy ∨ g = rg) ∧
      (∀ g, epCross α β N g ↔ g = ix ∨ g = iy ∨ g = ps) ∧
      (∀ g, epCross α β C g ↔ g = ox ∨ g = oy ∨ g = ps) ∧
      (ix ≠ iy ∧ ix ≠ ps ∧ iy ≠ ps ∧ ox ≠ oy ∧ ox ≠ ps ∧ oy ≠ ps ∧ ix ≠ ox ∧ iy ≠ oy ∧
        ix ≠ oy ∧ iy ≠ ox ∧ rg ≠ ix ∧ rg ≠ iy ∧ rg ≠ ox ∧ rg ≠ oy) ∧
      ((α rg = x ∧ β rg = y) ∨ (α rg = y ∧ β rg = x)) := by
  have hCch : C ∈ epChildren 𝒮 N := by rw [hch]; exact Finset.mem_singleton_self C
  obtain ⟨hCS, hCN, -⟩ := (mem_epChildren 𝒮 N C).mp hCch
  obtain ⟨hNL, hNne, hrN, -⟩ := hdec.2.1 N hN
  obtain ⟨hCL, ⟨c₀, hc₀⟩, -, -⟩ := hdec.2.1 C hCS
  have hNneL : N ≠ L := fun h' => hrN (h' ▸ hr)
  have hatom : epAtom 𝒮 N = N \ C := by
    rw [ep_atom_children, hch, Finset.singleton_biUnion]; rfl
  have hnode := hdec.2.2 N (Finset.mem_insert_of_mem hN)
  rw [hatom, hch, Finset.card_singleton, if_neg hNneL] at hnode
  have hAne : (epAtom 𝒮 N).Nonempty := by rw [hatom]; exact Finset.card_pos.mp (by omega)
  have hAY := ep_atom_notMem_refined α β L r 𝒮 𝒴 hdec href N C hN hCch hAne
  -- the atom has two vertices
  have hA2 : (N \ C).card = 2 := by
    obtain ⟨α', β', L', newE, hreach, h4, -, -, hcard, -, -⟩ :=
      ep_max_decomp_hub α β L r 𝒮 𝒴 h hb hconn hr hdec href hmax N
        (Finset.mem_insert_of_mem hN) hAne hAY
    rw [hatom] at hcard
    have hne' : C ≠ L \ N := by
      intro h'
      have : c₀ ∈ L \ N := h' ▸ hc₀
      exact (Finset.mem_sdiff.mp this).2 (hCN.1 hc₀)
    have hsub : ({C, L \ N} : Finset (Finset W)) ⊆
        (epHubFam 𝒮 L N).filter (fun D => (epCut α β D).card = 3) := by
      intro D hD
      rw [Finset.mem_insert, Finset.mem_singleton] at hD
      rw [Finset.mem_filter, mem_epHubFam]
      rcases hD with rfl | rfl
      · exact ⟨Or.inl hCch, hdC⟩
      · refine ⟨Or.inr ⟨hNneL, rfl⟩, ?_⟩
        have : epCut α β (L \ N) = epCut α β N := by
          ext g; rw [mem_epCut, mem_epCut]
          exact epD_cross_compl α β L N (L \ N) h (fun w => Finset.mem_sdiff) g
        rw [this]; exact hdN
    have h2 := Finset.card_le_card hsub
    rw [Finset.card_pair hne'] at h2
    have h5 : L'.card < 6 := by
      by_contra h'
      exact hnc ⟨α', β', L', hreach, h4, by omega⟩
    have p1 := epD_cut_parity α β L h N hNL
    have p2 := epD_cut_parity α β L h C hCL
    have p3 := Finset.card_sdiff_of_subset hCN.1
    have p4 := Finset.card_le_card hCN.1
    omega
  obtain ⟨x, y, hxy, hAxy⟩ := Finset.card_eq_two.mp hA2
  have hxA : x ∈ N \ C := by rw [hAxy]; exact Finset.mem_insert_self _ _
  have hyA : y ∈ N \ C := by rw [hAxy]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  obtain ⟨hxN, hxC⟩ := Finset.mem_sdiff.mp hxA
  obtain ⟨hyN, hyC⟩ := Finset.mem_sdiff.mp hyA
  have hxL := hNL hxN
  have hyL := hNL hyN
  have hNeq : ∀ w, w ∈ N ↔ w ∈ C ∨ w = x ∨ w = y := by
    intro w
    constructor
    · intro hw
      by_cases hwC : w ∈ C
      · exact Or.inl hwC
      · have : w ∈ N \ C := Finset.mem_sdiff.mpr ⟨hw, hwC⟩
        rw [hAxy, Finset.mem_insert, Finset.mem_singleton] at this
        exact Or.inr this
    · rintro (hw | rfl | rfl)
      · exact hCN.1 hw
      · exact hxN
      · exact hyN
  have hcompl : ∀ Z : Finset W, epCut α β (L \ Z) = epCut α β Z := by
    intro Z; ext g; rw [mem_epCut, mem_epCut]
    exact epD_cross_compl α β L Z (L \ Z) h (fun w => Finset.mem_sdiff) g
  have hge2 : ∀ Z : Finset W, Z ⊆ L → Z.Nonempty → Z ≠ L → 2 ≤ (epCut α β Z).card :=
    fun Z => ep_cut_ge_two α β L hb hconn Z
  -- no set with a cut of size two can be inserted into the node
  have noins : ∀ Z : Finset W, Z ⊆ N → (C ⊆ Z ∨ Disjoint C Z) → (epCut α β Z).card = 2 →
      2 ≤ ((N \ C) ∩ Z).card + (if C ⊆ Z then 1 else 0) →
      1 ≤ ((N \ C) \ Z).card + (if Disjoint C Z then 1 else 0) → False := by
    intro Z hZN hCZ hZ2 hin hout
    obtain ⟨k1, k2, k3⟩ := ep_decomp_insert α β L r 𝒮 hdec hr N Z (Finset.mem_insert_of_mem hN)
      hZN (fun h' => hrN (hZN h')) (Or.inl hZ2)
      (fun D hD => by rw [hch, Finset.mem_singleton] at hD; rw [hD]; exact hCZ)
      (by rw [hatom, hch, Finset.filter_singleton]
          by_cases hc : C ⊆ Z
          · rw [if_pos hc] at hin ⊢; rw [Finset.card_singleton]; exact hin
          · rw [if_neg hc] at hin ⊢; rw [Finset.card_empty]; exact hin)
      (by rw [hatom, hch, Finset.filter_singleton, if_neg hNneL]
          by_cases hc : Disjoint C Z
          · rw [if_pos hc] at hout ⊢; rw [Finset.card_singleton]; omega
          · rw [if_neg hc] at hout ⊢; rw [Finset.card_empty]; omega)
    have := hmax _ k2 (k3 𝒴 href hAY)
    rw [Finset.card_insert_of_notMem k1] at this
    omega
  -- disjointness facts
  have hdCx : Disjoint C ({x} : Finset W) := Finset.disjoint_singleton_right.mpr hxC
  have hdCy : Disjoint C ({y} : Finset W) := Finset.disjoint_singleton_right.mpr hyC
  have hdxy : Disjoint ({x} : Finset W) {y} := Finset.disjoint_singleton.mpr hxy
  have hdUx : Disjoint (L \ N) ({x} : Finset W) :=
    Finset.disjoint_singleton_right.mpr (fun h' => (Finset.mem_sdiff.mp h').2 hxN)
  have hdUy : Disjoint (L \ N) ({y} : Finset W) :=
    Finset.disjoint_singleton_right.mpr (fun h' => (Finset.mem_sdiff.mp h').2 hyN)
  have hdUC : Disjoint (L \ N) C := by
    rw [Finset.disjoint_left]; intro w hw hw'
    exact (Finset.mem_sdiff.mp hw).2 (hCN.1 hw')
  -- the sets `C ∪ {y}` and `C ∪ {x}`
  have hside : ∀ p q : W, p ≠ q → p ∈ N → p ∉ C → q ∈ N → q ∉ C →
      (∀ w, w ∈ N ↔ w ∈ C ∨ w = p ∨ w = q) →
      (epCut α β (C ∪ {q})).card + 2 * (epBtw α β C {q}).card = 6 ∧
      3 + 2 * (epBtw α β (C ∪ {q}) {p}).card = (epCut α β (C ∪ {q})).card + 3 ∧
      (epCut α β (C ∪ {q})).card + 2 * (epBtw α β (L \ N) {p}).card = 6 ∧
      4 ≤ (epCut α β (C ∪ {q})).card := by
    intro p q hpq hpN hpC hqN hqC hNpq
    have hdq : Disjoint C ({q} : Finset W) := Finset.disjoint_singleton_right.mpr hqC
    have e2 := ep_cut_union α β C {q} hdq
    rw [hdC, h.2 q (hNL hqN)] at e2
    have hdp : Disjoint (C ∪ {q}) ({p} : Finset W) := by
      rw [Finset.disjoint_singleton_right, Finset.mem_union, Finset.mem_singleton]
      exact fun h' => h'.elim hpC hpq
    have hNe : C ∪ {q} ∪ {p} = N := by
      ext w
      rw [hNpq, Finset.mem_union, Finset.mem_union, Finset.mem_singleton, Finset.mem_singleton]
      tauto
    have e1 := ep_cut_union α β (C ∪ {q}) {p} hdp
    rw [hNe, hdN, h.2 p (hNL hpN)] at e1
    have hdUp : Disjoint (L \ N) ({p} : Finset W) :=
      Finset.disjoint_singleton_right.mpr (fun h' => (Finset.mem_sdiff.mp h').2 hpN)
    have hUe : L \ N ∪ {p} = L \ (C ∪ {q}) := by
      ext w
      rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff, hNpq, Finset.mem_union,
        Finset.mem_singleton, Finset.mem_singleton]
      constructor
      · rintro (⟨a1, a2⟩ | rfl)
        · exact ⟨a1, fun h' => a2 (h'.elim Or.inl (fun h'' => Or.inr (Or.inr h'')))⟩
        · exact ⟨hNL hpN, fun h' => h'.elim hpC hpq⟩
      · rintro ⟨a1, a2⟩
        by_cases hwp : w = p
        · exact Or.inr hwp
        · exact Or.inl ⟨a1, fun h' => h'.elim (fun h'' => a2 (Or.inl h''))
            (fun h'' => h''.elim hwp (fun h''' => a2 (Or.inr h''')))⟩
    have e3 := ep_cut_union α β (L \ N) {p} hdUp
    rw [hUe, hcompl, hcompl, hdN, h.2 p (hNL hpN)] at e3
    have hZL : C ∪ {q} ⊆ L := Finset.union_subset hCL (Finset.singleton_subset_iff.mpr (hNL hqN))
    have hZne : C ∪ {q} ≠ L := fun h' => by
      have : p ∈ C ∪ {q} := h' ▸ hNL hpN
      rw [Finset.mem_union, Finset.mem_singleton] at this
      exact this.elim hpC hpq
    have g2 := hge2 _ hZL ⟨q, Finset.mem_union_right _ (Finset.mem_singleton_self q)⟩ hZne
    have hne2 : (epCut α β (C ∪ {q})).card ≠ 2 := by
      intro h2
      refine noins (C ∪ {q}) ?_ (Or.inl Finset.subset_union_left) h2 ?_ ?_
      · intro w hw
        rw [Finset.mem_union, Finset.mem_singleton] at hw
        exact hw.elim (fun h' => hCN.1 h') (fun h' => h' ▸ hqN)
      · rw [if_pos Finset.subset_union_left]
        have : 0 < ((N \ C) ∩ (C ∪ {q})).card := Finset.card_pos.mpr ⟨q, Finset.mem_inter.mpr
          ⟨Finset.mem_sdiff.mpr ⟨hqN, hqC⟩, Finset.mem_union_right _ (Finset.mem_singleton_self q)⟩⟩
        omega
      · have : 0 < ((N \ C) \ (C ∪ {q})).card := Finset.card_pos.mpr ⟨p, Finset.mem_sdiff.mpr
          ⟨Finset.mem_sdiff.mpr ⟨hpN, hpC⟩, fun h' => by
            rw [Finset.mem_union, Finset.mem_singleton] at h'
            exact h'.elim hpC hpq⟩⟩
        omega
    exact ⟨e2, e1, e3, by omega⟩
  obtain ⟨sx1, sx2, sx3, sx4⟩ := hside x y hxy hxN hxC hyN hyC hNeq
  obtain ⟨sy1, sy2, sy3, sy4⟩ := hside y x (Ne.symm hxy) hyN hyC hxN hxC
    (fun w => by rw [hNeq]; tauto)
  -- the atom itself
  have e4 := ep_cut_union α β {x} {y} hdxy
  rw [h.2 x hxL, h.2 y hyL] at e4
  have hAcut : (epCut α β ({x} ∪ {y} : Finset W)).card ≠ 2 := by
    intro h2
    have hAe : ({x} ∪ {y} : Finset W) = N \ C := by
      rw [hAxy]; ext w; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    rw [hAe] at h2
    refine noins (N \ C) Finset.sdiff_subset (Or.inr Finset.sdiff_disjoint.symm) h2 ?_ ?_
    · rw [Finset.inter_self, hA2]; omega
    · rw [if_pos Finset.sdiff_disjoint.symm]; omega
  have hAge : 2 ≤ (epCut α β ({x} ∪ {y} : Finset W)).card :=
    hge2 _ (Finset.union_subset (Finset.singleton_subset_iff.mpr hxL)
      (Finset.singleton_subset_iff.mpr hyL)) ⟨x, Finset.mem_union_left _ (Finset.mem_singleton_self x)⟩
      (fun h' => by
        have : c₀ ∈ ({x} ∪ {y} : Finset W) := h' ▸ hCL hc₀
        rw [Finset.mem_union, Finset.mem_singleton, Finset.mem_singleton] at this
        rcases this with rfl | rfl
        · exact hxC hc₀
        · exact hyC hc₀)
  have u1 := ep_btw_union_le α β {x} C {y}
  have u2 := ep_btw_union_le α β {y} C {x}
  rw [ep_btw_comm α β {x} (C ∪ {y}), ep_btw_comm α β {x} C] at u1
  rw [ep_btw_comm α β {y} (C ∪ {x}), ep_btw_comm α β {y} C, ep_btw_comm α β {y} {x}] at u2
  -- all the numbers are one
  have n1 : (epBtw α β C {x}).card = 1 := by omega
  have n2 : (epBtw α β C {y}).card = 1 := by omega
  have n3 : (epBtw α β {x} {y}).card = 1 := by omega
  have n4 : (epBtw α β (L \ N) {x}).card = 1 := by omega
  have n5 : (epBtw α β (L \ N) {y}).card = 1 := by omega
  have n6 : (epBtw α β (L \ N) C).card = 1 := by
    have e6 := ep_cut_union α β (L \ N) C hdUC
    have hUC : L \ N ∪ C = L \ ({x} ∪ {y}) := by
      ext w
      rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff, hNeq, Finset.mem_union,
        Finset.mem_singleton, Finset.mem_singleton]
      constructor
      · rintro (⟨a1, a2⟩ | a1)
        · exact ⟨a1, fun h' => a2 (Or.inr h')⟩
        · exact ⟨hCL a1, fun h' => h'.elim (fun h'' => hxC (h'' ▸ a1)) (fun h'' => hyC (h'' ▸ a1))⟩
      · rintro ⟨a1, a2⟩
        by_cases hwC : w ∈ C
        · exact Or.inr hwC
        · exact Or.inl ⟨a1, fun h' => h'.elim hwC a2⟩
    rw [hUC, hcompl, hcompl, hdN, hdC] at e6
    omega
  obtain ⟨ox, hox⟩ := Finset.card_eq_one.mp n1
  obtain ⟨oy, hoy⟩ := Finset.card_eq_one.mp n2
  obtain ⟨rg, hrg⟩ := Finset.card_eq_one.mp n3
  obtain ⟨ix, hix⟩ := Finset.card_eq_one.mp n4
  obtain ⟨iy, hiy⟩ := Finset.card_eq_one.mp n5
  obtain ⟨ps, hps⟩ := Finset.card_eq_one.mp n6
  have mox : ox ∈ epBtw α β C {x} := by rw [hox]; exact Finset.mem_singleton_self _
  have moy : oy ∈ epBtw α β C {y} := by rw [hoy]; exact Finset.mem_singleton_self _
  have mrg : rg ∈ epBtw α β {x} {y} := by rw [hrg]; exact Finset.mem_singleton_self _
  have mix : ix ∈ epBtw α β (L \ N) {x} := by rw [hix]; exact Finset.mem_singleton_self _
  have miy : iy ∈ epBtw α β (L \ N) {y} := by rw [hiy]; exact Finset.mem_singleton_self _
  have mps : ps ∈ epBtw α β (L \ N) C := by rw [hps]; exact Finset.mem_singleton_self _
  have comm : ∀ (P Q : Finset W) (g : E), g ∈ epBtw α β P Q → g ∈ epBtw α β Q P :=
    fun P Q g hg => by rw [ep_btw_comm]; exact hg
  have incut : ∀ (P Q : Finset W) (g : E), Disjoint P Q → g ∈ epBtw α β P Q →
      g ∈ epCut α β P := by
    intro P Q g hPQ hg
    rw [mem_epBtw] at hg
    rw [mem_epCut]
    unfold epCross
    rcases hg with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · exact Or.inl ⟨a1, fun h' => Finset.disjoint_left.mp hPQ h' a2⟩
    · exact Or.inr ⟨fun h' => Finset.disjoint_left.mp hPQ h' a1, a2⟩
  -- distinctness
  have d_ix_iy : ix ≠ iy := fun h' =>
    ep_btw_disj α β (L \ N) {x} {y} ix mix (h' ▸ miy) hdUx hdUy hdxy
  have d_ix_ps : ix ≠ ps := fun h' =>
    ep_btw_disj α β (L \ N) {x} C ix mix (h' ▸ mps) hdUx hdUC hdCx.symm
  have d_iy_ps : iy ≠ ps := fun h' =>
    ep_btw_disj α β (L \ N) {y} C iy miy (h' ▸ mps) hdUy hdUC hdCy.symm
  have d_ox_oy : ox ≠ oy := fun h' =>
    ep_btw_disj α β C {x} {y} ox mox (h' ▸ moy) hdCx hdCy hdxy
  have d_ox_ps : ox ≠ ps := fun h' =>
    ep_btw_disj α β C {x} (L \ N) ox mox (h' ▸ comm _ _ _ mps) hdCx hdUC.symm hdUx.symm
  have d_oy_ps : oy ≠ ps := fun h' =>
    ep_btw_disj α β C {y} (L \ N) oy moy (h' ▸ comm _ _ _ mps) hdCy hdUC.symm hdUy.symm
  have d_ix_ox : ix ≠ ox := fun h' =>
    ep_btw_disj α β {x} (L \ N) C ix (comm _ _ _ mix) (h' ▸ comm _ _ _ mox) hdUx.symm
      hdCx.symm hdUC
  have d_iy_oy : iy ≠ oy := fun h' =>
    ep_btw_disj α β {y} (L \ N) C iy (comm _ _ _ miy) (h' ▸ comm _ _ _ moy) hdUy.symm
      hdCy.symm hdUC
  have d_rg_ix : rg ≠ ix := fun h' =>
    ep_btw_disj α β {x} {y} (L \ N) rg mrg (h' ▸ comm _ _ _ mix) hdxy hdUx.symm hdUy.symm
  have d_rg_ox : rg ≠ ox := fun h' =>
    ep_btw_disj α β {x} {y} C rg mrg (h' ▸ comm _ _ _ mox) hdxy hdCx.symm hdCy.symm
  have d_rg_iy : rg ≠ iy := fun h' =>
    ep_btw_disj α β {y} {x} (L \ N) rg (comm _ _ _ mrg) (h' ▸ comm _ _ _ miy) hdxy.symm
      hdUy.symm hdUx.symm
  have d_rg_oy : rg ≠ oy := fun h' =>
    ep_btw_disj α β {y} {x} C rg (comm _ _ _ mrg) (h' ▸ comm _ _ _ moy) hdxy.symm
      hdCy.symm hdCx.symm
  have d_ix_oy : ix ≠ oy := by
    intro h'
    have a := mix
    have b := moy
    rw [← h', mem_epBtw] at b
    rw [mem_epBtw] at a
    simp only [Finset.mem_singleton] at a b
    rcases a with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases b with ⟨b1, b2⟩ | ⟨b1, b2⟩
    · exact hxy (a2.symm.trans b2)
    · exact hxC (a2 ▸ b2)
    · exact hxC (a1 ▸ b1)
    · exact hxy (a1.symm.trans b1)
  have d_iy_ox : iy ≠ ox := by
    intro h'
    have a := miy
    have b := mox
    rw [← h', mem_epBtw] at b
    rw [mem_epBtw] at a
    simp only [Finset.mem_singleton] at a b
    rcases a with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases b with ⟨b1, b2⟩ | ⟨b1, b2⟩
    · exact hxy (b2.symm.trans a2)
    · exact hyC (a2 ▸ b2)
    · exact hyC (a1 ▸ b1)
    · exact hxy (b1.symm.trans a1)
  -- the four stars
  have hUN : ∀ g, g ∈ epBtw α β (L \ N) C ∨ g ∈ epBtw α β (L \ N) {x} ∨
      g ∈ epBtw α β (L \ N) {y} → g ∈ epCut α β N := by
    intro g hg
    rw [← hcompl N]
    rcases hg with h' | h' | h'
    · exact incut _ _ g hdUC h'
    · exact incut _ _ g hdUx h'
    · exact incut _ _ g hdUy h'
  refine ⟨x, y, rg, ix, iy, ox, oy, ps, hxy, hAxy, fun g => ?_, fun g => ?_, fun g => ?_,
    fun g => ?_, ⟨d_ix_iy, d_ix_ps, d_iy_ps, d_ox_oy, d_ox_ps, d_oy_ps, d_ix_ox, d_iy_oy,
      d_ix_oy, d_iy_ox, d_rg_ix, d_rg_iy, d_rg_ox, d_rg_oy⟩, ?_⟩
  · rw [← mem_epCut]
    exact ep_three_mem _ (h.2 x hxL) ix ox rg (incut _ _ _ hdUx.symm (comm _ _ _ mix))
      (incut _ _ _ hdCx.symm (comm _ _ _ mox)) (incut _ _ _ hdxy mrg) d_ix_ox
      (Ne.symm d_rg_ix) (Ne.symm d_rg_ox) g
  · rw [← mem_epCut]
    exact ep_three_mem _ (h.2 y hyL) iy oy rg (incut _ _ _ hdUy.symm (comm _ _ _ miy))
      (incut _ _ _ hdCy.symm (comm _ _ _ moy)) (incut _ _ _ hdxy.symm (comm _ _ _ mrg)) d_iy_oy
      (Ne.symm d_rg_iy) (Ne.symm d_rg_oy) g
  · rw [← mem_epCut]
    exact ep_three_mem _ hdN ix iy ps (hUN _ (Or.inr (Or.inl mix))) (hUN _ (Or.inr (Or.inr miy)))
      (hUN _ (Or.inl mps)) d_ix_iy d_ix_ps d_iy_ps g
  · rw [← mem_epCut]
    exact ep_three_mem _ hdC ox oy ps (incut _ _ _ hdCx mox) (incut _ _ _ hdCy moy)
      (incut _ _ _ hdUC.symm (comm _ _ _ mps)) d_ox_oy d_ox_ps d_oy_ps g
  · rw [mem_epBtw] at mrg
    simpa only [Finset.mem_singleton] using mrg

lemma ep_fin3_fun {E : Type*} (a b c : E) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ f : Fin 3 → E, Function.Injective f ∧ ∀ g, (∃ j, f j = g) ↔ g = a ∨ g = b ∨ g = c := by
  refine ⟨![a, b, c], ?_, fun g => ⟨?_, ?_⟩⟩
  · intro j j' hjj'
    fin_cases j <;> fin_cases j' <;> simp_all
  · rintro ⟨j, rfl⟩
    fin_cases j <;> simp
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

set_option maxHeartbeats 6400000 in
open Classical in
/-- **From a chain of the decomposition to a ladder.** A chain `N 0 ⊋ N 1 ⊋ … ⊋ N n` of
members of a `𝒴`-maximum decomposition of a multigraph without a core, each the only child of
the previous one and all with cuts of size three, is a ladder with `n` rungs. -/
theorem ep_chain_ladder {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (r : W)
    (𝒮 𝒴 : Finset (Finset W)) (h : EpCubicD α β L) (hb : EpBridgeless α β L)
    (hconn : EpConnected α β L) (hr : r ∈ L) (hdec : EpDecomp α β L r 𝒮)
    (href : EpRefines L r 𝒮 𝒴)
    (hmax : ∀ 𝒮', EpDecomp α β L r 𝒮' → EpRefines L r 𝒮' 𝒴 → 𝒮'.card ≤ 𝒮.card)
    (hnc : ¬EpHasCore α β L) (n : ℕ) (N : ℕ → Finset W) (hNS : ∀ i, i ≤ n → N i ∈ 𝒮)
    (hchild : ∀ i, i < n → epChildren 𝒮 (N i) = {N (i + 1)})
    (hcut : ∀ i, i ≤ n → (epCut α β (N i)).card = 3) :
    ∃ (k : ℕ → Fin 3) (v : ℕ → Fin 3 → W) (cut : ℕ → Fin 3 → E) (rung : ℕ → E),
      EpLadder α β (N 0 \ N n) n k v cut rung := by
  obtain ⟨a, b, c, hab, hac, hbc, hset⟩ := Finset.card_eq_three.mp (hcut 0 (Nat.zero_le n))
  -- the rung nodes
  have hnode : ∀ m, ∃ (x y : W) (rg ix iy ox oy ps : E), m < n →
      (x ≠ y ∧ N m \ N (m + 1) = {x, y} ∧
      (∀ g, epCross α β {x} g ↔ g = ix ∨ g = ox ∨ g = rg) ∧
      (∀ g, epCross α β {y} g ↔ g = iy ∨ g = oy ∨ g = rg) ∧
      (∀ g, epCross α β (N m) g ↔ g = ix ∨ g = iy ∨ g = ps) ∧
      (∀ g, epCross α β (N (m + 1)) g ↔ g = ox ∨ g = oy ∨ g = ps) ∧
      (ix ≠ iy ∧ ix ≠ ps ∧ iy ≠ ps ∧ ox ≠ oy ∧ ox ≠ ps ∧ oy ≠ ps ∧ ix ≠ ox ∧ iy ≠ oy ∧
        ix ≠ oy ∧ iy ≠ ox ∧ rg ≠ ix ∧ rg ≠ iy ∧ rg ≠ ox ∧ rg ≠ oy) ∧
      ((α rg = x ∧ β rg = y) ∨ (α rg = y ∧ β rg = x))) := by
    intro m
    by_cases hm : m < n
    · obtain ⟨x, y, rg, ix, iy, ox, oy, ps, hP⟩ := ep_rung_node α β L r 𝒮 𝒴 h hb hconn hr hdec
        href hmax hnc (N m) (N (m + 1)) (hNS m (by omega)) (hchild m hm) (hcut m (by omega))
        (hcut (m + 1) (by omega))
      exact ⟨x, y, rg, ix, iy, ox, oy, ps, fun _ => hP⟩
    · exact ⟨r, r, a, a, a, a, a, a, fun h' => absurd h' hm⟩
  choose x y rg ix iy ox oy ps hP using hnode
  -- the labelled cuts
  obtain ⟨c0, hc0inj, hc0rng⟩ := ep_fin3_fun a b c hab hac hbc
  obtain ⟨cut, hcut0, hcutS⟩ : ∃ cut : ℕ → Fin 3 → E, cut 0 = c0 ∧
      ∀ m j, cut (m + 1) j = if cut m j = ix m then ox m else
        if cut m j = iy m then oy m else cut m j :=
    ⟨fun m => Nat.rec c0 (fun m prev j => if prev j = ix m then ox m else
      if prev j = iy m then oy m else prev j) m, rfl, fun m j => rfl⟩
  have hInv0 : Function.Injective (cut 0) ∧ ∀ g, epCross α β (N 0) g ↔ ∃ j, cut 0 j = g := by
    rw [hcut0]
    refine ⟨hc0inj, fun g => ?_⟩
    rw [hc0rng, ← mem_epCut, hset, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
  -- values of the next cut
  have hval : ∀ m, m < n → (∀ g, epCross α β (N m) g ↔ ∃ j, cut m j = g) → ∀ j,
      (cut m j = ix m ∧ cut (m + 1) j = ox m) ∨ (cut m j = iy m ∧ cut (m + 1) j = oy m) ∨
      (cut m j = ps m ∧ cut (m + 1) j = ps m) := by
    intro m hm hrng j
    obtain ⟨-, -, -, -, hcN, -, ⟨d1, d2, d3, -⟩, -⟩ := hP m hm
    rcases (hcN (cut m j)).mp ((hrng _).mpr ⟨j, rfl⟩) with h' | h' | h'
    · exact Or.inl ⟨h', by rw [hcutS, if_pos h']⟩
    · exact Or.inr (Or.inl ⟨h', by
        rw [hcutS, if_neg (fun h'' => d1 (h''.symm.trans h')), if_pos h']⟩)
    · exact Or.inr (Or.inr ⟨h', by
        rw [hcutS, if_neg (fun h'' => d2 (h''.symm.trans h')),
          if_neg (fun h'' => d3 (h''.symm.trans h')), h']⟩)
  have hInv : ∀ m, m ≤ n → Function.Injective (cut m) ∧
      ∀ g, epCross α β (N m) g ↔ ∃ j, cut m j = g := by
    intro m
    induction m with
    | zero => exact fun _ => hInv0
    | succ m ih =>
      intro hm
      obtain ⟨hinj, hrng⟩ := ih (by omega)
      have hv := hval m (by omega) hrng
      obtain ⟨-, -, -, -, hcN, hcC, ⟨d1, d2, d3, d4, d5, d6, -⟩, -⟩ := hP m (by omega)
      refine ⟨fun j j' hjj' => ?_, fun g => ?_⟩
      · rcases hv j with ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
          rcases hv j' with ⟨b1, b2⟩ | ⟨b1, b2⟩ | ⟨b1, b2⟩
        · exact hinj (a1.trans b1.symm)
        · exact absurd (a2.symm.trans (hjj'.trans b2)) d4
        · exact absurd (a2.symm.trans (hjj'.trans b2)) d5
        · exact absurd (b2.symm.trans (hjj'.symm.trans a2)) d4
        · exact hinj (a1.trans b1.symm)
        · exact absurd (a2.symm.trans (hjj'.trans b2)) d6
        · exact absurd (b2.symm.trans (hjj'.symm.trans a2)) d5
        · exact absurd (b2.symm.trans (hjj'.symm.trans a2)) d6
        · exact hinj (a1.trans b1.symm)
      · rw [hcC]
        constructor
        · rintro (rfl | rfl | rfl)
          · obtain ⟨j, hj⟩ := (hrng _).mp ((hcN _).mpr (Or.inl rfl))
            rcases hv j with ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩
            · exact ⟨j, a2⟩
            · exact absurd (hj.symm.trans a1) d1
            · exact absurd (hj.symm.trans a1) d2
          · obtain ⟨j, hj⟩ := (hrng _).mp ((hcN _).mpr (Or.inr (Or.inl rfl)))
            rcases hv j with ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩
            · exact absurd (a1.symm.trans hj) d1
            · exact ⟨j, a2⟩
            · exact absurd (hj.symm.trans a1) d3
          · obtain ⟨j, hj⟩ := (hrng _).mp ((hcN _).mpr (Or.inr (Or.inr rfl)))
            rcases hv j with ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩
            · exact absurd (a1.symm.trans hj) d2
            · exact absurd (a1.symm.trans hj) d3
            · exact ⟨j, a2⟩
        · rintro ⟨j, rfl⟩
          rcases hv j with ⟨-, a2⟩ | ⟨-, a2⟩ | ⟨-, a2⟩
          · exact Or.inl a2
          · exact Or.inr (Or.inl a2)
          · exact Or.inr (Or.inr a2)
  have hv' : ∀ m, m < n → ∀ j,
      (cut m j = ix m ∧ cut (m + 1) j = ox m) ∨ (cut m j = iy m ∧ cut (m + 1) j = oy m) ∨
      (cut m j = ps m ∧ cut (m + 1) j = ps m) := fun m hm =>
    hval m hm (hInv m (by omega)).2
  -- the passing rail
  have hkex : ∀ m, ∃ j : Fin 3, m < n → cut m j = ps m := by
    intro m
    by_cases hm : m < n
    · obtain ⟨-, -, -, -, hcN, -, -, -⟩ := hP m hm
      obtain ⟨j, hj⟩ := ((hInv m (by omega)).2 _).mp ((hcN _).mpr (Or.inr (Or.inr rfl)))
      exact ⟨j, fun _ => hj⟩
    · exact ⟨0, fun h' => absurd h' hm⟩
  choose k hk using hkex
  -- nestedness of the chain
  have hstep : ∀ i, i < n → N (i + 1) ⊂ N i := by
    intro i hi
    have : N (i + 1) ∈ epChildren 𝒮 (N i) := by
      rw [hchild i hi]; exact Finset.mem_singleton_self _
    exact ((mem_epChildren 𝒮 (N i) _).mp this).2.1
  have hmono : ∀ i i', i ≤ i' → i' ≤ n → N i' ⊆ N i := by
    intro i i' hii'
    induction i', hii' using Nat.le_induction with
    | base => exact fun _ => Finset.Subset.refl _
    | succ i' hi' ih => exact fun hn => (hstep i' (by omega)).1.trans (ih (by omega))
  have hNL : ∀ i, i ≤ n → N i ⊆ L := fun i hi => (hdec.2.1 (N i) (hNS i hi)).1
  have hxyA : ∀ m, m < n → ∀ w, (w ∈ N m ∧ w ∉ N (m + 1)) ↔ w = x m ∨ w = y m := by
    intro m hm w
    obtain ⟨-, hA, -⟩ := hP m hm
    rw [← Finset.mem_sdiff, hA, Finset.mem_insert, Finset.mem_singleton]
  have hAdisj : ∀ m m' w, m < m' → m' < n → (w ∈ N m ∧ w ∉ N (m + 1)) →
      (w ∈ N m' ∧ w ∉ N (m' + 1)) → False := by
    intro m m' w hmm' hm' h1 h2
    exact h1.2 (hmono (m + 1) m' (by omega) (by omega) h2.1)
  have hAeq : ∀ m m' w, m < n → m' < n → (w ∈ N m ∧ w ∉ N (m + 1)) →
      (w ∈ N m' ∧ w ∉ N (m' + 1)) → m = m' := by
    intro m m' w hm hm' h1 h2
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact hAdisj m m' w hlt hm' h1 h2
    · exact hAdisj m' m w hlt hm h2 h1
  have hAX : ∀ m, m < n → ∀ w, (w ∈ N m ∧ w ∉ N (m + 1)) → w ∈ N 0 \ N n := by
    intro m hm w hw
    exact Finset.mem_sdiff.mpr ⟨hmono 0 m (Nat.zero_le _) (by omega) hw.1,
      fun h' => hw.2 (hmono (m + 1) n (by omega) (le_refl n) h')⟩
  -- the vertices
  obtain ⟨v, hv⟩ : ∃ v : ℕ → Fin 3 → W, ∀ m j, v m j = if cut m j = ix m then x m else y m :=
    ⟨_, fun _ _ => rfl⟩
  have hvA : ∀ m, m < n → ∀ j, v m j ∈ N m ∧ v m j ∉ N (m + 1) := by
    intro m hm j
    rw [hxyA m hm, hv]
    by_cases hc : cut m j = ix m
    · rw [if_pos hc]; exact Or.inl rfl
    · rw [if_neg hc]; exact Or.inr rfl
  have hrgA : ∀ m, m < n → ((α (rg m) ∈ N m ∧ α (rg m) ∉ N (m + 1)) ∧
      (β (rg m) ∈ N m ∧ β (rg m) ∉ N (m + 1))) := by
    intro m hm
    obtain ⟨-, -, -, -, -, -, -, hrg⟩ := hP m hm
    rcases hrg with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact ⟨(hxyA m hm _).mpr (Or.inl e1), (hxyA m hm _).mpr (Or.inr e2)⟩
    · exact ⟨(hxyA m hm _).mpr (Or.inr e1), (hxyA m hm _).mpr (Or.inl e2)⟩
  have hrg_nocross : ∀ m, m < n → ∀ m', m' ≤ n → ¬epCross α β (N m') (rg m) := by
    intro m hm m' hm' hcr
    obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := hrgA m hm
    unfold epCross at hcr
    rcases Nat.lt_or_ge m m' with hlt | hge
    · have ha : α (rg m) ∉ N m' := fun h' => a2 (hmono (m + 1) m' (by omega) hm' h')
      have hb' : β (rg m) ∉ N m' := fun h' => b2 (hmono (m + 1) m' (by omega) hm' h')
      tauto
    · have ha : α (rg m) ∈ N m' := hmono m' m hge (by omega) a1
      have hb' : β (rg m) ∈ N m' := hmono m' m hge (by omega) b1
      tauto
  refine ⟨k, v, cut, rg, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the passing rail keeps its edge
    intro m hm
    rcases hv' m hm (k m) with ⟨a1, -⟩ | ⟨a1, -⟩ | ⟨a1, a2⟩
    · obtain ⟨-, -, -, -, -, -, ⟨-, d2, -⟩, -⟩ := hP m hm
      exact absurd (a1.symm.trans (hk m hm)) d2
    · obtain ⟨-, -, -, -, -, -, ⟨-, -, d3, -⟩, -⟩ := hP m hm
      exact absurd (a1.symm.trans (hk m hm)) d3
    · rw [a2, a1]
  · -- the three edges at a vertex
    intro m hm j hj g
    obtain ⟨-, -, hsx, hsy, -, -, ⟨d1, -⟩, -⟩ := hP m hm
    rcases hv' m hm j with ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, -⟩
    · rw [hv, if_pos a1, a1, a2]; exact hsx g
    · rw [hv, if_neg (fun h' => d1 (h'.symm.trans a1)), a1, a2]; exact hsy g
    · exact absurd ((hInv m (by omega)).1 (a1.trans (hk m hm).symm)) hj
  · intro m hm j hj
    obtain ⟨-, -, -, -, -, -, ⟨-, -, -, -, -, -, d7, d8, -⟩, -⟩ := hP m hm
    rcases hv' m hm j with ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, -⟩
    · rw [a1, a2]; exact d7
    · rw [a1, a2]; exact d8
    · exact absurd ((hInv m (by omega)).1 (a1.trans (hk m hm).symm)) hj
  · intro m hm m' hm' j hrc
    exact hrg_nocross m hm m' hm' (((hInv m' hm').2 _).mpr ⟨j, hrc.symm⟩)
  · intro m hm m' hm' hrr
    have h1 := (hrgA m hm).1
    have h2 := (hrgA m' hm').1
    rw [← hrr] at h2
    exact hAeq m m' _ hm hm' h1 h2
  · -- the vertex set
    intro w
    constructor
    · intro hw
      obtain ⟨hw0, hwn⟩ := Finset.mem_sdiff.mp hw
      have hfind : ∀ d, d ≤ n → w ∉ N d → ∃ m, m < d ∧ w ∈ N m ∧ w ∉ N (m + 1) := by
        intro d
        induction d with
        | zero => exact fun _ h' => absurd hw0 h'
        | succ d ih =>
          intro hd hwd
          by_cases hwd' : w ∈ N d
          · exact ⟨d, Nat.lt_succ_self d, hwd', hwd⟩
          · obtain ⟨m, a1, a2⟩ := ih (by omega) hwd'
            exact ⟨m, by omega, a2⟩
      obtain ⟨m, hm, hwA⟩ := hfind n (le_refl n) hwn
      obtain ⟨-, -, -, -, hcN, -, ⟨d1, d2, d3, -⟩, -⟩ := hP m hm
      rcases (hxyA m hm w).mp hwA with rfl | rfl
      · obtain ⟨j, hj⟩ := ((hInv m (by omega)).2 _).mp ((hcN _).mpr (Or.inl rfl))
        refine ⟨m, hm, j, fun h' => d2 (hj.symm.trans (h' ▸ hk m hm)), ?_⟩
        rw [hv, if_pos hj]
      · obtain ⟨j, hj⟩ := ((hInv m (by omega)).2 _).mp ((hcN _).mpr (Or.inr (Or.inl rfl)))
        refine ⟨m, hm, j, fun h' => d3 (hj.symm.trans (h' ▸ hk m hm)), ?_⟩
        rw [hv, if_neg (fun h' => d1 (h'.symm.trans hj))]
    · rintro ⟨m, hm, j, -, rfl⟩
      exact hAX m hm _ (hvA m hm j)
  · intro m hm m' hm' j j' _ _ hvv
    have h1 := hvA m hm j
    have h2 := hvA m' hm' j'
    rw [← hvv] at h2
    exact hAeq m m' _ hm hm' h1 h2
  · -- equal edges of two cuts
    intro m m' j j' hmm'
    induction m', hmm' using Nat.le_induction generalizing j' with
    | base =>
      intro hm hcc
      exact ⟨(hInv m hm).1 hcc, fun i h1 h2 => by omega⟩
    | succ m' hmm' ih =>
      intro hm' hcc
      have hcr1 : epCross α β (N m) (cut m j) := ((hInv m (by omega)).2 _).mpr ⟨j, rfl⟩
      have hcr2 : epCross α β (N (m' + 1)) (cut m j) :=
        ((hInv (m' + 1) hm').2 _).mpr ⟨j', hcc.symm⟩
      -- the edge crosses `N m'` as well
      have hcr3 : epCross α β (N m') (cut m j) := by
        have s1 := hmono m m' hmm' (by omega)
        have s2 := (hstep m' (by omega)).1
        unfold epCross at hcr1 hcr2 ⊢
        rcases hcr2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · have : β (cut m j) ∉ N m := by
            have := s1 (s2 e1); tauto
          exact Or.inl ⟨s2 e1, fun h' => this (s1 h')⟩
        · have : α (cut m j) ∉ N m := by
            have := s1 (s2 e2); tauto
          exact Or.inr ⟨fun h' => this (s1 h'), s2 e2⟩
      obtain ⟨j'', hj''⟩ := ((hInv m' (by omega)).2 _).mp hcr3
      obtain ⟨-, -, -, -, -, hcC, ⟨-, -, -, -, -, -, d7, d8, d9, d10, -⟩, -⟩ := hP m' (by omega)
      -- so it is the passing edge of the node `m'`
      have hps : cut m' j'' = ps m' := by
        rcases hv' m' (by omega) j'' with ⟨a1, -⟩ | ⟨a1, -⟩ | ⟨a1, -⟩
        · rw [← hj'', hcC, a1] at hcr2
          rcases hcr2 with h' | h' | h'
          · exact absurd h' d7
          · exact absurd h' d9
          · exact a1.trans h'
        · rw [← hj'', hcC, a1] at hcr2
          rcases hcr2 with h' | h' | h'
          · exact absurd h' d10
          · exact absurd h' d8
          · exact a1.trans h'
        · exact a1
      have hj''k : j'' = k m' := (hInv m' (by omega)).1 (hps.trans (hk m' (by omega)).symm)
      have hj'k : j' = k m' := by
        apply (hInv (m' + 1) hm').1
        rcases hv' m' (by omega) (k m') with ⟨a1, -⟩ | ⟨a1, -⟩ | ⟨-, a2⟩
        · obtain ⟨-, -, -, -, -, -, ⟨-, d2, -⟩, -⟩ := hP m' (by omega)
          exact absurd (a1.symm.trans (hk m' (by omega))) d2
        · obtain ⟨-, -, -, -, -, -, ⟨-, -, d3, -⟩, -⟩ := hP m' (by omega)
          exact absurd (a1.symm.trans (hk m' (by omega))) d3
        · rw [a2, ← hps, hj'', hcc]
      obtain ⟨e1, e2⟩ := ih j'' (by omega) hj''.symm
      refine ⟨by rw [e1, hj''k, hj'k], fun i h1 h2 => ?_⟩
      rcases Nat.lt_or_ge i m' with hlt | hge
      · exact e2 i h1 hlt
      · have : i = m' := by omega
        rw [this, e1, hj''k]
  · intro m hm
    exact ⟨hAX m hm _ (hrgA m hm).1, hAX m hm _ (hrgA m hm).2⟩
  · intro g hg
    have hgL : α g ∈ L := hNL 0 (Nat.zero_le _) (Finset.mem_sdiff.mp hg).1
    rcases h.1 g with h' | h'
    · exact h'.2.2
    · exact absurd hgL h'.1

set_option maxHeartbeats 3200000 in
open Classical in
/-- **Corollary 21 (new form).** In a `𝒴`-maximum decomposition of a multigraph without a
core, a chain of 41 nodes, each the only child of the previous one, gives a burl. -/
theorem ep_chain_burl {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (r : W)
    (𝒮 𝒴 : Finset (Finset W)) (h : EpCubicD α β L) (hb : EpBridgeless α β L)
    (hconn : EpConnected α β L) (hr : r ∈ L) (hdec : EpDecomp α β L r 𝒮)
    (href : EpRefines L r 𝒮 𝒴)
    (hmax : ∀ 𝒮', EpDecomp α β L r 𝒮' → EpRefines L r 𝒮' 𝒴 → 𝒮'.card ≤ 𝒮.card)
    (hnc : ¬EpHasCore α β L) (N : ℕ → Finset W) (hNS : ∀ i, i ≤ 41 → N i ∈ 𝒮)
    (hchild : ∀ i, i < 41 → epChildren 𝒮 (N i) = {N (i + 1)}) :
    EpBurl α β (N 0 \ N 41) := by
  have hstep : ∀ i, i < 41 → N (i + 1) ⊂ N i := by
    intro i hi
    have : N (i + 1) ∈ epChildren 𝒮 (N i) := by
      rw [hchild i hi]; exact Finset.mem_singleton_self _
    exact ((mem_epChildren 𝒮 (N i) _).mp this).2.1
  have hmono : ∀ i i', i ≤ i' → i' ≤ 41 → N i' ⊆ N i := by
    intro i i' hii'
    induction i', hii' using Nat.le_induction with
    | base => exact fun _ => Finset.Subset.refl _
    | succ i' hi' ih => exact fun hn => (hstep i' (by omega)).1.trans (ih (by omega))
  have hstrict : ∀ i i', i < i' → i' ≤ 41 → N i' ⊂ N i := fun i i' hii' hi' =>
    lt_of_le_of_lt (hmono (i + 1) i' (by omega) hi') (hstep i (by omega))
  have hNL : ∀ i, i ≤ 41 → N i ⊆ L := fun i hi => (hdec.2.1 (N i) (hNS i hi)).1
  have hX₀L : N 0 \ N 41 ⊆ L := Finset.sdiff_subset.trans (hNL 0 (by omega))
  have hnl : ∀ g, α g ∈ N 0 \ N 41 → α g ≠ β g := by
    intro g hg
    rcases h.1 g with h' | h'
    · exact h'.2.2
    · exact absurd (hX₀L hg) h'.1
  have hsub : ∀ i i', i ≤ i' → i' ≤ 41 → N i \ N i' ⊆ N 0 \ N 41 := fun i i' hii' hi' =>
    Finset.sdiff_subset_sdiff (hmono 0 i (Nat.zero_le _) (by omega)) (hmono i' 41 hi' (le_refl _))
  have hcuts : ∀ i, i ≤ 41 → (epCut α β (N i)).card = 2 ∨ (epCut α β (N i)).card = 3 :=
    fun i hi => (hdec.2.1 (N i) (hNS i hi)).2.2.2
  by_cases h3 : ∃ a b c, a < b ∧ b < c ∧ c ≤ 41 ∧ (epCut α β (N a)).card = 2 ∧
      (epCut α β (N b)).card = 2 ∧ (epCut α β (N c)).card = 2
  · -- three cuts of size two
    obtain ⟨a, b, c, hab, hbc, hc, ha2, hb2, hc2⟩ := h3
    obtain ⟨-, hne, hrN, -⟩ := hdec.2.1 (N c) (hNS c hc)
    have hrNa := (hdec.2.1 (N a) (hNS a (by omega))).2.2.1
    exact ep_burl_mono α β _ _ (hsub a c (by omega) hc) hnl
      (ep_nested2_burl α β L (N a) (N b) (N c) h hb hconn (hNL a (by omega))
        (fun h' => hrNa (h' ▸ hr)) (hstrict a b hab (by omega)) (hstrict b c hbc hc) hne
        ha2 hb2 hc2)
  · -- fourteen consecutive cuts of size three
    have hblock : ∃ s, s + 13 ≤ 41 ∧ ∀ i, s ≤ i → i ≤ s + 13 → (epCut α β (N i)).card = 3 := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨a, a1, a2, a3⟩ := hcon 0 (by omega)
      obtain ⟨b, b1, b2, b3⟩ := hcon 14 (by omega)
      obtain ⟨c, c1, c2, c3⟩ := hcon 28 (by omega)
      exact h3 ⟨a, b, c, by omega, by omega, by omega,
        (hcuts a (by omega)).resolve_right a3, (hcuts b (by omega)).resolve_right b3,
        (hcuts c (by omega)).resolve_right c3⟩
    obtain ⟨s, hs, hs3⟩ := hblock
    obtain ⟨k, v, cut, rung, hl⟩ := ep_chain_ladder α β L r 𝒮 𝒴 h hb hconn hr hdec href hmax hnc
      13 (fun i => N (s + i)) (fun i hi => hNS (s + i) (by omega))
      (fun i hi => hchild (s + i) (by omega)) (fun i hi => hs3 (s + i) (by omega) (by omega))
    have hburl := ep_ladder_burl α β _ 13 k v cut rung hl (le_refl 13)
    exact ep_burl_mono α β _ _ (hsub s (s + 13) (by omega) hs) hnl hburl

set_option maxHeartbeats 1600000 in
/-- Three pairwise disjoint sets `U`, `A`, `C` covering the vertices, with no edge between `A`
and `U`: every edge crossing `A` or `U` crosses `C`, and no edge crosses both `A` and `U`. -/
lemma ep_three_part_cut {W E : Type*} (α β : E → W) (L U A C : Finset W)
    (hlive : ∀ g, α g ≠ β g → α g ∈ L ∧ β g ∈ L) (htri : ∀ w, w ∈ L → w ∈ U ∨ w ∈ A ∨ w ∈ C)
    (hUA : ∀ w, w ∈ U → w ∉ A) (hUC : ∀ w, w ∈ U → w ∉ C) (hAC : ∀ w, w ∈ A → w ∉ C)
    (hno : ∀ g, ¬(α g ∈ A ∧ β g ∈ U) ∧ ¬(α g ∈ U ∧ β g ∈ A)) (g : E) :
    (epCross α β A g → epCross α β C g) ∧ (epCross α β U g → epCross α β C g) ∧
      (epCross α β U g → ¬epCross α β A g) := by
  by_cases hne : α g = β g
  · unfold epCross; rw [hne]; tauto
  · obtain ⟨l1, l2⟩ := hlive g hne
    have n1 := (hno g).1
    have n2 := (hno g).2
    have a1 := hUA (α g)
    have a2 := hUC (α g)
    have a3 := hAC (α g)
    have b1 := hUA (β g)
    have b2 := hUC (β g)
    have b3 := hAC (β g)
    unfold epCross
    rcases htri _ l1 with t1 | t1 | t1 <;> rcases htri _ l2 with t2 | t2 | t2 <;> tauto

set_option maxHeartbeats 3200000 in
open Classical in
/-- **Atoms of degree-2 nodes** (the claim inside the proof of Lemma 11). In a `𝒴`-maximum
decomposition of a multigraph without a core, a member `N` with a single child `C` has an atom
with at most two vertices, and with exactly one vertex if one of the two cuts has size two. -/
theorem ep_deg2_atom_card {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (r : W)
    (𝒮 𝒴 : Finset (Finset W)) (h : EpCubicD α β L) (hb : EpBridgeless α β L)
    (hconn : EpConnected α β L) (hr : r ∈ L) (hdec : EpDecomp α β L r 𝒮)
    (href : EpRefines L r 𝒮 𝒴)
    (hmax : ∀ 𝒮', EpDecomp α β L r 𝒮' → EpRefines L r 𝒮' 𝒴 → 𝒮'.card ≤ 𝒮.card)
    (hnc : ¬EpHasCore α β L) (N C : Finset W) (hN : N ∈ 𝒮) (hch : epChildren 𝒮 N = {C}) :
    1 ≤ (N \ C).card ∧ (N \ C).card ≤ 2 ∧
      (((epCut α β N).card = 2 ∨ (epCut α β C).card = 2) → (N \ C).card = 1) := by
  have hCch : C ∈ epChildren 𝒮 N := by rw [hch]; exact Finset.mem_singleton_self C
  obtain ⟨hCS, hCN, -⟩ := (mem_epChildren 𝒮 N C).mp hCch
  obtain ⟨hNL, hNne, hrN, hNcut⟩ := hdec.2.1 N hN
  obtain ⟨hCL, ⟨c₀, hc₀⟩, -, hCcut⟩ := hdec.2.1 C hCS
  have hNneL : N ≠ L := fun h' => hrN (h' ▸ hr)
  have hatom : epAtom 𝒮 N = N \ C := by
    rw [ep_atom_children, hch, Finset.singleton_biUnion]; rfl
  have hnode := hdec.2.2 N (Finset.mem_insert_of_mem hN)
  rw [hatom, hch, Finset.card_singleton, if_neg hNneL] at hnode
  have hA1 : 1 ≤ (N \ C).card := by omega
  have hAne : (epAtom 𝒮 N).Nonempty := by rw [hatom]; exact Finset.card_pos.mp hA1
  have hAY := ep_atom_notMem_refined α β L r 𝒮 𝒴 hdec href N C hN hCch hAne
  have hge2 : ∀ Z : Finset W, Z ⊆ L → Z.Nonempty → Z ≠ L → 2 ≤ (epCut α β Z).card :=
    fun Z => ep_cut_ge_two α β L hb hconn Z
  have hlive : ∀ g, α g ≠ β g → α g ∈ L ∧ β g ∈ L := by
    intro g hg
    rcases h.1 g with h' | h'
    · exact ⟨h'.1, h'.2.1⟩
    · exact absurd h'.2.symm hg
  -- a set between `C` and `N` with a small cut cannot exist
  have noins : ∀ Z : Finset W, Z ⊆ N → C ⊆ Z → (epCut α β Z).card ≤ 3 →
      1 ≤ ((N \ C) ∩ Z).card → 1 ≤ ((N \ C) \ Z).card → False := by
    intro Z hZN hCZ hZ3 hin hout
    have hZL : Z ⊆ L := hZN.trans hNL
    have hZ2 := hge2 Z hZL ⟨c₀, hCZ hc₀⟩ (fun h' => hrN (hZN (h' ▸ hr)))
    obtain ⟨k1, k2, k3⟩ := ep_decomp_insert α β L r 𝒮 hdec hr N Z (Finset.mem_insert_of_mem hN)
      hZN (fun h' => hrN (hZN h')) (by omega)
      (fun D hD => by rw [hch, Finset.mem_singleton] at hD; rw [hD]; exact Or.inl hCZ)
      (by rw [hatom, hch, Finset.filter_singleton, if_pos hCZ, Finset.card_singleton]; omega)
      (by rw [hatom, hch, Finset.filter_singleton, if_neg hNneL]
          have : 0 ≤ (if Disjoint C Z then ({C} : Finset (Finset W)) else ∅).card :=
            Nat.zero_le _
          omega)
    have := hmax _ k2 (k3 𝒴 href hAY)
    rw [Finset.card_insert_of_notMem k1] at this
    omega
  have hAL : N \ C ⊆ L := Finset.sdiff_subset.trans hNL
  have hAneL : N \ C ≠ L := fun h' => hrN ((Finset.mem_sdiff.mp (h' ▸ hr : r ∈ N \ C)).1)
  have hdA := hge2 (N \ C) hAL (Finset.card_pos.mp hA1) hAneL
  -- the three kinds of vertices
  have htri : ∀ w, w ∈ L → w ∈ L \ N ∨ w ∈ N \ C ∨ w ∈ C := by
    intro w hw
    by_cases h1 : w ∈ N
    · by_cases h2 : w ∈ C
      · exact Or.inr (Or.inr h2)
      · exact Or.inr (Or.inl (Finset.mem_sdiff.mpr ⟨h1, h2⟩))
    · exact Or.inl (Finset.mem_sdiff.mpr ⟨hw, h1⟩)
  have hone : ((epCut α β N).card = 2 ∨ (epCut α β C).card = 2) → (N \ C).card = 1 := by
    intro h2
    by_contra hcard
    have hA2 : 2 ≤ (N \ C).card := by omega
    rcases h2 with hN2 | hC2
    · -- a vertex of the atom with an edge leaving `N`
      have hex : ∃ v ∈ N \ C, 1 ≤ (epBtw α β (L \ N) {v}).card := by
        by_contra hcon
        push_neg at hcon
        have hnoAU : ∀ g, ¬(α g ∈ N \ C ∧ β g ∈ L \ N) ∧ ¬(α g ∈ L \ N ∧ β g ∈ N \ C) := by
          intro g
          constructor
          · rintro ⟨a1, a2⟩
            have : g ∈ epBtw α β (L \ N) {α g} :=
              (mem_epBtw _ _ _ _ _).mpr (Or.inr ⟨Finset.mem_singleton_self _, a2⟩)
            have := Finset.card_pos.mpr ⟨g, this⟩
            have := hcon _ a1
            omega
          · rintro ⟨a1, a2⟩
            have : g ∈ epBtw α β (L \ N) {β g} :=
              (mem_epBtw _ _ _ _ _).mpr (Or.inl ⟨a1, Finset.mem_singleton_self _⟩)
            have := Finset.card_pos.mpr ⟨g, this⟩
            have := hcon _ a2
            omega
        have hpart := ep_three_part_cut α β L (L \ N) (N \ C) C hlive htri
          (fun w hw hw' => (Finset.mem_sdiff.mp hw).2 (Finset.mem_sdiff.mp hw').1)
          (fun w hw hw' => (Finset.mem_sdiff.mp hw).2 (hCN.1 hw'))
          (fun w hw => (Finset.mem_sdiff.mp hw).2) hnoAU
        have hcomplN : epCut α β (L \ N) = epCut α β N := by
          ext g; rw [mem_epCut, mem_epCut]
          exact epD_cross_compl α β L N (L \ N) h (fun w => Finset.mem_sdiff) g
        have hsub : epCut α β (L \ N) ∪ epCut α β (N \ C) ⊆ epCut α β C := by
          intro g hg
          rw [mem_epCut]
          rcases Finset.mem_union.mp hg with hg | hg
          · exact (hpart g).2.1 ((mem_epCut _ _ _ _).mp hg)
          · exact (hpart g).1 ((mem_epCut _ _ _ _).mp hg)
        have hdis : Disjoint (epCut α β (L \ N)) (epCut α β (N \ C)) := by
          rw [Finset.disjoint_left]
          intro g hg1 hg2
          exact (hpart g).2.2 ((mem_epCut _ _ _ _).mp hg1) ((mem_epCut _ _ _ _).mp hg2)
        have := Finset.card_le_card hsub
        rw [Finset.card_union_of_disjoint hdis, hcomplN] at this
        rcases hCcut with h' | h' <;> omega
      obtain ⟨v, hvA, hv1⟩ := hex
      obtain ⟨hvN, hvC⟩ := Finset.mem_sdiff.mp hvA
      have hdUv : Disjoint (L \ N) ({v} : Finset W) :=
        Finset.disjoint_singleton_right.mpr (fun h' => (Finset.mem_sdiff.mp h').2 hvN)
      have e1 := ep_cut_union α β (L \ N) {v} hdUv
      have hUe : L \ N ∪ {v} = L \ (N \ {v}) := by
        ext w
        simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]
        constructor
        · rintro (⟨a1, a2⟩ | rfl)
          · exact ⟨a1, fun h' => a2 h'.1⟩
          · exact ⟨hNL hvN, fun h' => h'.2 rfl⟩
        · rintro ⟨a1, a2⟩
          by_cases hwv : w = v
          · exact Or.inr hwv
          · exact Or.inl ⟨a1, fun h' => a2 ⟨h', hwv⟩⟩
      have hcompl : ∀ Z : Finset W, epCut α β (L \ Z) = epCut α β Z := by
        intro Z; ext g; rw [mem_epCut, mem_epCut]
        exact epD_cross_compl α β L Z (L \ Z) h (fun w => Finset.mem_sdiff) g
      rw [hUe, hcompl, hcompl, hN2, h.2 v (hNL hvN)] at e1
      obtain ⟨w, hwA, hwv⟩ : ∃ w ∈ N \ C, w ≠ v := by
        by_contra hcon
        push_neg at hcon
        have : N \ C ⊆ {v} := fun w hw => Finset.mem_singleton.mpr (hcon w hw)
        have := Finset.card_le_card this
        rw [Finset.card_singleton] at this
        omega
      refine noins (N \ {v}) Finset.sdiff_subset (fun w hw => Finset.mem_sdiff.mpr
        ⟨hCN.1 hw, fun h' => hvC (Finset.mem_singleton.mp h' ▸ hw)⟩) (by omega) ?_ ?_
      · exact Finset.card_pos.mpr ⟨w, Finset.mem_inter.mpr ⟨hwA, Finset.mem_sdiff.mpr
          ⟨(Finset.mem_sdiff.mp hwA).1, fun h' => hwv (Finset.mem_singleton.mp h')⟩⟩⟩
      · exact Finset.card_pos.mpr ⟨v, Finset.mem_sdiff.mpr ⟨hvA,
          fun h' => (Finset.mem_sdiff.mp h').2 (Finset.mem_singleton_self v)⟩⟩
    · -- a vertex of the atom with an edge into `C`
      have hex : ∃ v ∈ N \ C, 1 ≤ (epBtw α β C {v}).card := by
        by_contra hcon
        push_neg at hcon
        have hnoAC : ∀ g, ¬(α g ∈ N \ C ∧ β g ∈ C) ∧ ¬(α g ∈ C ∧ β g ∈ N \ C) := by
          intro g
          constructor
          · rintro ⟨a1, a2⟩
            have : g ∈ epBtw α β C {α g} :=
              (mem_epBtw _ _ _ _ _).mpr (Or.inr ⟨Finset.mem_singleton_self _, a2⟩)
            have := Finset.card_pos.mpr ⟨g, this⟩
            have := hcon _ a1
            omega
          · rintro ⟨a1, a2⟩
            have : g ∈ epBtw α β C {β g} :=
              (mem_epBtw _ _ _ _ _).mpr (Or.inl ⟨a1, Finset.mem_singleton_self _⟩)
            have := Finset.card_pos.mpr ⟨g, this⟩
            have := hcon _ a2
            omega
        have hpart := ep_three_part_cut α β L C (N \ C) (L \ N) hlive
          (fun w hw => by rcases htri w hw with t | t | t <;> tauto)
          (fun w hw hw' => (Finset.mem_sdiff.mp hw').2 hw)
          (fun w hw hw' => (Finset.mem_sdiff.mp hw').2 (hCN.1 hw))
          (fun w hw hw' => (Finset.mem_sdiff.mp hw').2 (Finset.mem_sdiff.mp hw).1) hnoAC
        have hcomplN : epCut α β (L \ N) = epCut α β N := by
          ext g; rw [mem_epCut, mem_epCut]
          exact epD_cross_compl α β L N (L \ N) h (fun w => Finset.mem_sdiff) g
        have hsub : epCut α β C ∪ epCut α β (N \ C) ⊆ epCut α β (L \ N) := by
          intro g hg
          rw [mem_epCut]
          rcases Finset.mem_union.mp hg with hg | hg
          · exact (hpart g).2.1 ((mem_epCut _ _ _ _).mp hg)
          · exact (hpart g).1 ((mem_epCut _ _ _ _).mp hg)
        have hdis : Disjoint (epCut α β C) (epCut α β (N \ C)) := by
          rw [Finset.disjoint_left]
          intro g hg1 hg2
          exact (hpart g).2.2 ((mem_epCut _ _ _ _).mp hg1) ((mem_epCut _ _ _ _).mp hg2)
        have := Finset.card_le_card hsub
        rw [Finset.card_union_of_disjoint hdis, hcomplN] at this
        rcases hNcut with h' | h' <;> omega
      obtain ⟨v, hvA, hv1⟩ := hex
      obtain ⟨hvN, hvC⟩ := Finset.mem_sdiff.mp hvA
      have hdCv : Disjoint C ({v} : Finset W) := Finset.disjoint_singleton_right.mpr hvC
      have e1 := ep_cut_union α β C {v} hdCv
      rw [hC2, h.2 v (hNL hvN)] at e1
      obtain ⟨w, hwA, hwv⟩ : ∃ w ∈ N \ C, w ≠ v := by
        by_contra hcon
        push_neg at hcon
        have : N \ C ⊆ {v} := fun w hw => Finset.mem_singleton.mpr (hcon w hw)
        have := Finset.card_le_card this
        rw [Finset.card_singleton] at this
        omega
      refine noins (C ∪ {v}) (Finset.union_subset hCN.1 (Finset.singleton_subset_iff.mpr hvN))
        Finset.subset_union_left (by omega) ?_ ?_
      · exact Finset.card_pos.mpr ⟨v, Finset.mem_inter.mpr ⟨hvA,
          Finset.mem_union_right _ (Finset.mem_singleton_self v)⟩⟩
      · refine Finset.card_pos.mpr ⟨w, Finset.mem_sdiff.mpr ⟨hwA, fun h' => ?_⟩⟩
        rcases Finset.mem_union.mp h' with h'' | h''
        · exact (Finset.mem_sdiff.mp hwA).2 h''
        · exact hwv (Finset.mem_singleton.mp h'')
  refine ⟨hA1, ?_, hone⟩
  by_cases h2 : (epCut α β N).card = 2 ∨ (epCut α β C).card = 2
  · rw [hone h2]; omega
  · push_neg at h2
    obtain ⟨x, y, -, -, -, -, -, -, hxy, hA, -⟩ := ep_rung_node α β L r 𝒮 𝒴 h hb hconn hr hdec
      href hmax hnc N C hN hch (hNcut.resolve_left h2.1) (hCcut.resolve_left h2.2)
    rw [hA, Finset.card_pair hxy]

open Classical in
/-- A triangle of a 3-cut contraction that avoids the new vertex is a triangle of the original
multigraph, disjoint from the contracted set. -/
theorem epCon_triangle_back {W E : Type*} [Fintype E] (α β : E → W) (L X : Finset W)
    (x₀ x₁ : W) (hx₀ : x₀ ∈ X) (hx₁ : x₁ ∈ X) (p q r : W) (e1 e2 e3 : E)
    (ht : EpTriangle (epConA α β X x₀ x₁) (epConB α β X x₀ x₁) (epL' L X x₀) p q r e1 e2 e3)
    (hp : p ≠ x₀) (hq : q ≠ x₀) (hr : r ≠ x₀) :
    EpTriangle α β L p q r e1 e2 e3 ∧ p ∉ X ∧ q ∉ X ∧ r ∉ X := by
  obtain ⟨hpL, hqL, hrL, hpq, hqr, hpr, h1, h2, h3⟩ := ht
  have hout : ∀ w, w ∈ epL' L X x₀ → w ≠ x₀ → w ∈ L ∧ w ∉ X := by
    intro w hw hwp
    unfold epL' at hw
    rcases Finset.mem_insert.mp hw with h' | h'
    · exact absurd h' hwp
    · exact Finset.mem_sdiff.mp h'
  obtain ⟨hpL', hpX⟩ := hout p hpL hp
  obtain ⟨hqL', hqX⟩ := hout q hqL hq
  obtain ⟨hrL', hrX⟩ := hout r hrL hr
  have hedge : ∀ (e : E) (a b : W), a ≠ b → a ∉ X → b ∉ X →
      (∀ w, epCross (epConA α β X x₀ x₁) (epConB α β X x₀ x₁) {w} e ↔ w = a ∨ w = b) →
      ∀ w, epCross α β {w} e ↔ w = a ∨ w = b := by
    intro e a b hab ha hb he w
    apply ep_edge_cross α β a b e hab
    rcases ep_edge_ends _ _ a b e hab he with h' | h'
    · exact Or.inl (epCon_ends_out α β X x₀ x₁ hx₀ hx₁ e a b ha hb h')
    · exact Or.inr (epCon_ends_out α β X x₀ x₁ hx₀ hx₁ e b a hb ha h')
  exact ⟨⟨hpL', hqL', hrL', hpq, hqr, hpr, hedge e1 p q hpq hpX hqX h1,
    hedge e2 q r hqr hqX hrX h2, hedge e3 r p (Ne.symm hpr) hrX hpX h3⟩, hpX, hqX, hrX⟩

open Classical in
/-- An edge not inside the contracted set joins the images of its ends. -/
lemma epCon_adj {W E : Type*} (α β : E → W) (X : Finset W) (x₀ x₁ : W) (g : E) (p q : W)
    (hin : ¬(α g ∈ X ∧ β g ∈ X)) (hg : (α g = p ∧ β g = q) ∨ (α g = q ∧ β g = p)) :
    EpAdj (epConA α β X x₀ x₁) (epConB α β X x₀ x₁) (epRho X x₀ p) (epRho X x₀ q) := by
  refine ⟨g, ?_⟩
  unfold epConA epConB
  rw [if_neg hin, if_neg hin]
  rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨by rw [h1], by rw [h2]⟩
  · exact Or.inr ⟨by rw [h1], by rw [h2]⟩

open Classical in
/-- A vertex of a triangle has only one edge besides the two triangle edges. -/
lemma ep_triangle_one_out {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (h : EpCubicD α β L) (x y z : W) (exy eyz ezx : E)
    (ht : EpTriangle α β L x y z exy eyz ezx) (g g' : E) (hg : epCross α β {x} g)
    (hg' : epCross α β {x} g') (h1 : g ≠ exy) (h2 : g ≠ ezx) (h3 : g' ≠ exy) (h4 : g' ≠ ezx) :
    g = g' := by
  obtain ⟨hx, hy, hz, hxy, hyz, hxz, c1, c2, c3⟩ := ht
  by_contra hne
  have hee : exy ≠ ezx := by
    intro he
    have := (c1 y).mpr (Or.inr rfl)
    rw [he, c3] at this
    exact this.elim hyz (fun h' => hxy h'.symm)
  have hsub : ({exy, ezx, g, g'} : Finset E) ⊆ epCut α β {x} := by
    intro w hw
    rw [mem_epCut]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact (c1 x).mpr (Or.inl rfl)
    · exact (c3 x).mpr (Or.inr rfl)
    · exact hg
    · exact hg'
  have hcard : ({exy, ezx, g, g'} : Finset E).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hne]
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      exact fun h' => h'.elim (fun h'' => h2 h''.symm) (fun h'' => h4 h''.symm)
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (h' | h' | h')
      · exact hee h'
      · exact h1 h'.symm
      · exact h3 h'.symm
  have := Finset.card_le_card hsub
  rw [hcard, h.2 x hx] at this
  omega

set_option maxHeartbeats 1600000 in
open Classical in
/-- **Relevance is preserved by contractions.** A relevant triangle disjoint from a contracted
set is relevant in the contraction. -/
theorem epCon_relevant {W E : Type*} [Fintype E] (α β : E → W) (L X : Finset W) (x₀ x₁ : W)
    (h : EpCubicD α β L) (hx₀ : x₀ ∈ X) (x y z : W) (exy eyz ezx : E)
    (ht : EpTriangle α β L x y z exy eyz ezx) (hxX : x ∉ X) (hyX : y ∉ X) (hzX : z ∉ X)
    (hrel : ¬EpIrrelevant α β x y z) :
    ¬EpIrrelevant (epConA α β X x₀ x₁) (epConB α β X x₀ x₁) x y z := by
  intro hirr'
  have hTmem : ∀ w, w ∈ ({x, y, z} : Finset W) ↔ w = x ∨ w = y ∨ w = z := by
    intro w; simp only [Finset.mem_insert, Finset.mem_singleton]
  have hTX : ∀ w, w ∈ ({x, y, z} : Finset W) → w ∉ X := by
    intro w hw
    rcases (hTmem w).mp hw with rfl | rfl | rfl <;> assumption
  have hTL : ∀ w, w ∈ ({x, y, z} : Finset W) → w ∈ L := by
    intro w hw
    rcases (hTmem w).mp hw with rfl | rfl | rfl
    · exact ht.1
    · exact ht.2.1
    · exact ht.2.2.1
  unfold EpIrrelevant at hrel
  push_neg at hrel
  obtain ⟨u, hu, v, hv, a, b, haT, hbT, ⟨g, hg⟩, ⟨g', hg'⟩, hab⟩ := hrel
  have hρT : ∀ w, w ∉ ({x, y, z} : Finset W) → epRho X x₀ w ∉ ({x, y, z} : Finset W) := by
    intro w hw
    unfold epRho
    by_cases hwX : w ∈ X
    · rw [if_pos hwX]; exact fun h' => hTX x₀ h' hx₀
    · rw [if_neg hwX]; exact hw
  have hρu : ∀ w, w ∈ ({x, y, z} : Finset W) → epRho X x₀ w = w := by
    intro w hw; unfold epRho; rw [if_neg (hTX w hw)]
  have hadj1 := epCon_adj α β X x₀ x₁ g u a
    (fun h' => by rcases hg with ⟨e1, -⟩ | ⟨-, e2⟩
                  · exact hTX u hu (e1 ▸ h'.1)
                  · exact hTX u hu (e2 ▸ h'.2)) hg
  have hadj2 := epCon_adj α β X x₀ x₁ g' v b
    (fun h' => by rcases hg' with ⟨e1, -⟩ | ⟨-, e2⟩
                  · exact hTX v hv (e1 ▸ h'.1)
                  · exact hTX v hv (e2 ▸ h'.2)) hg'
  rw [hρu u hu] at hadj1
  rw [hρu v hv] at hadj2
  obtain ⟨k1, k2⟩ := hirr' u hu v hv _ _ (hρT a haT) (hρT b hbT) hadj1 hadj2
  have hau : a ≠ u := fun h' => haT (h' ▸ hu)
  have hbv : b ≠ v := fun h' => hbT (h' ▸ hv)
  -- the two vertices of the triangle are different
  have huv : u ≠ v := by
    intro huv
    subst huv
    have hcr : ∀ (f : E) (c : W), c ≠ u → ((α f = u ∧ β f = c) ∨ (α f = c ∧ β f = u)) →
        epCross α β {u} f ∧ epCross α β {c} f := by
      intro f c hc hf
      rw [epCross_singleton, epCross_singleton]
      rcases hf with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact ⟨Or.inl ⟨e1, fun h' => hc (e2.symm.trans h')⟩,
          Or.inr ⟨fun h' => hc (h'.symm.trans e1), e2⟩⟩
      · exact ⟨Or.inr ⟨fun h' => hc (e1.symm.trans h'), e2⟩,
          Or.inl ⟨e1, fun h' => hc (h'.symm.trans e2)⟩⟩
    obtain ⟨cg, cga⟩ := hcr g a hau hg
    obtain ⟨cg', cgb⟩ := hcr g' b hbv hg'
    -- an edge crossing `{c}` with `c` outside the triangle is not a triangle edge
    have hnot : ∀ (p q r : W) (e1 e2 e3 : E), EpTriangle α β L p q r e1 e2 e3 →
        ({p, q, r} : Finset W) = {x, y, z} → ∀ (f : E) (c : W), c ∉ ({x, y, z} : Finset W) →
        epCross α β {c} f → f ≠ e1 ∧ f ≠ e3 := by
      intro p q r e1 e2 e3 ht' hset f c hc hf
      have hcp : c ≠ p := fun h' => hc (hset ▸ h' ▸ Finset.mem_insert_self _ _)
      have hcq : c ≠ q := fun h' => hc (hset ▸ h' ▸
        Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      have hcr' : c ≠ r := fun h' => hc (hset ▸ h' ▸ Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
      obtain ⟨-, -, -, -, -, -, c1, -, c3⟩ := ht'
      constructor
      · intro h'; rw [h', c1] at hf; exact hf.elim hcp hcq
      · intro h'; rw [h', c3] at hf; exact hf.elim hcr' hcp
    have hgg' : g = g' := by
      rcases (hTmem u).mp hu with rfl | rfl | rfl
      · obtain ⟨n1, n2⟩ := hnot u y z exy eyz ezx ht rfl g a haT cga
        obtain ⟨n3, n4⟩ := hnot u y z exy eyz ezx ht rfl g' b hbT cgb
        exact ep_triangle_one_out α β L h u y z exy eyz ezx ht g g' cg cg' n1 n2 n3 n4
      · have hset : ({u, z, x} : Finset W) = {x, u, z} := by
          ext w; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
        obtain ⟨n1, n2⟩ := hnot u z x eyz ezx exy ht.rot hset g a haT cga
        obtain ⟨n3, n4⟩ := hnot u z x eyz ezx exy ht.rot hset g' b hbT cgb
        exact ep_triangle_one_out α β L h u z x eyz ezx exy ht.rot g g' cg cg' n1 n2 n3 n4
      · have hset : ({u, x, y} : Finset W) = {x, y, u} := by
          ext w; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
        obtain ⟨n1, n2⟩ := hnot u x y ezx exy eyz ht.rot.rot hset g a haT cga
        obtain ⟨n3, n4⟩ := hnot u x y ezx exy eyz ht.rot.rot hset g' b hbT cgb
        exact ep_triangle_one_out α β L h u x y ezx exy eyz ht.rot.rot g g' cg cg' n1 n2 n3 n4
    subst hgg'
    have hab' : a = b := by
      rcases hg with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hg' with ⟨e3, e4⟩ | ⟨e3, e4⟩
      · exact e2.symm.trans e4
      · exact absurd (e3.symm.trans e1) hbv
      · exact absurd (e1.symm.trans e3) hau
      · exact e1.symm.trans e3
    obtain ⟨g'', hg''⟩ := hab (fun h' => absurd rfl h')
    subst hab'
    have haL : a ∈ L := by
      rcases h.1 g with ⟨l1, l2, -⟩ | ⟨l1, l2⟩
      · rcases hg with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · exact e2 ▸ l2
        · exact e1 ▸ l1
      · rcases hg with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · exact absurd (e1 ▸ hTL u hu) l1
        · exact absurd (e2 ▸ hTL u hu) (l2 ▸ l1)
    rcases h.1 g'' with ⟨-, -, l3⟩ | ⟨l1, -⟩
    · rcases hg'' with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> exact l3 (e1.trans e2.symm)
    · rcases hg'' with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> exact l1 (e1 ▸ haL)
  have hρne := k1 huv
  have hab'' : a ≠ b := fun h' => hρne (by rw [h'])
  obtain ⟨g'', hg''⟩ := hab (fun _ => hab'')
  by_cases hin : α g'' ∈ X ∧ β g'' ∈ X
  · apply hρne
    have haX : a ∈ X := by rcases hg'' with ⟨e1, -⟩ | ⟨-, e2⟩ <;> [exact e1 ▸ hin.1; exact e2 ▸ hin.2]
    have hbX : b ∈ X := by rcases hg'' with ⟨-, e2⟩ | ⟨e1, -⟩ <;> [exact e2 ▸ hin.2; exact e1 ▸ hin.1]
    unfold epRho
    rw [if_pos haX, if_pos hbX]
  · exact k2 (epCon_adj α β X x₀ x₁ g'' a b hin hg'')

/-- Pruned away from `r`: every irrelevant triangle contains the vertex `r`. -/
def EpPrunedAt {W E : Type*} (α β : E → W) (L : Finset W) (r : W) : Prop :=
  ∀ x y z exy eyz ezx, EpTriangle α β L x y z exy eyz ezx → EpIrrelevant α β x y z →
    x = r ∨ y = r ∨ z = r

/-- A twig: a set with a cut of size two, or with a cut of size three and at least five
vertices. -/
def EpTwig {W E : Type*} [Fintype E] (α β : E → W) (X : Finset W) : Prop :=
  (epCut α β X).card = 2 ∨ ((epCut α β X).card = 3 ∧ 5 ≤ X.card)

set_option maxHeartbeats 3200000 in
open Classical in
/-- **Leaves are small twigs.** In a `𝒴`-maximum decomposition (with `𝒴` a family of maximum
coverage) of a multigraph without a core that is pruned away from the root, every member
without children is a twig with at most eight vertices. -/
theorem ep_leaf_twig {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (r : W)
    (𝒮 𝒴 : Finset (Finset W)) (h : EpCubicD α β L) (hb : EpBridgeless α β L)
    (hconn : EpConnected α β L) (hr : r ∈ L) (hbig : 12 ≤ L.card)
    (hfam : EpTwigFam α β L 𝒴)
    (hcov : ∀ 𝒴', EpTwigFam α β L 𝒴' → (𝒴'.biUnion id).card ≤ (𝒴.biUnion id).card)
    (hdec : EpDecomp α β L r 𝒮) (href : EpRefines L r 𝒮 𝒴)
    (hmax : ∀ 𝒮', EpDecomp α β L r 𝒮' → EpRefines L r 𝒮' 𝒴 → 𝒮'.card ≤ 𝒮.card)
    (hnc : ¬EpHasCore α β L) (hpr : EpPrunedAt α β L r) (S : Finset W) (hS : S ∈ 𝒮)
    (hleaf : epChildren 𝒮 S = ∅) : EpTwig α β S ∧ S.card ≤ 8 := by
  obtain ⟨hSL, hSne, hrS, hScut⟩ := hdec.2.1 S hS
  have hSneL : S ≠ L := fun h' => hrS (h' ▸ hr)
  have hatom : epAtom 𝒮 S = S := by
    rw [ep_atom_children, hleaf, Finset.biUnion_empty, Finset.sdiff_empty]
  have hnode := hdec.2.2 S (Finset.mem_insert_of_mem hS)
  rw [hatom, hleaf, Finset.card_empty, if_neg hSneL] at hnode
  by_cases hSY : S ∈ 𝒴
  · obtain ⟨a1, a2, a3⟩ := (hfam.1 S hSY).2.facts
    rcases (hfam.1 S hSY).2 with ⟨b1, -, -⟩ | ⟨b1, b2⟩
    · exact ⟨Or.inl b1, a2⟩
    · exact ⟨Or.inr ⟨b1, by omega⟩, a2⟩
  · have hAY : epAtom 𝒮 S ∉ 𝒴 := by rw [hatom]; exact hSY
    have hAne : (epAtom 𝒮 S).Nonempty := by rw [hatom]; exact hSne
    obtain ⟨α', β', L', newE, hreach, h4, -, -, hcard, -, -⟩ :=
      ep_max_decomp_hub α β L r 𝒮 𝒴 h hb hconn hr hdec href hmax S
        (Finset.mem_insert_of_mem hS) hAne hAY
    rw [hatom] at hcard
    have h5 : L'.card < 6 := by
      by_contra h'
      exact hnc ⟨α', β', L', hreach, h4, by omega⟩
    rcases hScut with h2 | h3
    · exact ⟨Or.inl h2, by omega⟩
    · -- a cut of size three: the leaf would be a relevant triangle
      exfalso
      have hcomplS : epCut α β (L \ S) = epCut α β S := by
        ext g; rw [mem_epCut, mem_epCut]
        exact epD_cross_compl α β L S (L \ S) h (fun w => Finset.mem_sdiff) g
      have hf1 : 1 ≤ ((epHubFam 𝒮 L S).filter (fun C => (epCut α β C).card = 3)).card := by
        refine Finset.card_pos.mpr ⟨L \ S, Finset.mem_filter.mpr ⟨?_, by rw [hcomplS]; exact h3⟩⟩
        exact (mem_epHubFam 𝒮 L S _).mpr (Or.inr ⟨hSneL, rfl⟩)
      have hpar := epD_cut_parity α β L h S hSL
      have hS3 : S.card = 3 := by omega
      obtain ⟨x, y, z, hxy, hxz, hyz, hSeq⟩ := Finset.card_eq_three.mp hS3
      have hTmem : ∀ w, w ∈ S ↔ w = x ∨ w = y ∨ w = z := by
        intro w; rw [hSeq]; simp only [Finset.mem_insert, Finset.mem_singleton]
      have hxS : x ∈ S := (hTmem x).mpr (Or.inl rfl)
      have hyS : y ∈ S := (hTmem y).mpr (Or.inr (Or.inl rfl))
      have hzS : z ∈ S := (hTmem z).mpr (Or.inr (Or.inr rfl))
      -- no pair of vertices of the leaf has a cut of size two
      have hpair : ∀ p q s : W, p ∈ S → q ∈ S → s ∈ S → p ≠ q → p ≠ s → q ≠ s →
          (∀ w, w ∈ S ↔ w = p ∨ w = q ∨ w = s) →
          (epBtw α β {p} {q}).card ≤ 1 ∧
            3 ≤ (epBtw α β {p} {q}).card + (epBtw α β ({p} ∪ {q}) {s}).card := by
        intro p q s hp hq hs hpq hps hqs hmem
        have hd : Disjoint ({p} : Finset W) {q} := Finset.disjoint_singleton.mpr hpq
        have e1 := ep_cut_union α β {p} {q} hd
        rw [h.2 p (hSL hp), h.2 q (hSL hq)] at e1
        have hd2 : Disjoint ({p} ∪ {q} : Finset W) {s} := by
          rw [Finset.disjoint_singleton_right, Finset.mem_union, Finset.mem_singleton,
            Finset.mem_singleton]
          exact fun h' => h'.elim (fun h'' => hps h''.symm) (fun h'' => hqs h''.symm)
        have hSe : ({p} ∪ {q} ∪ {s} : Finset W) = S := by
          ext w
          rw [hmem, Finset.mem_union, Finset.mem_union, Finset.mem_singleton,
            Finset.mem_singleton, Finset.mem_singleton]
          tauto
        have e2 := ep_cut_union α β ({p} ∪ {q}) {s} hd2
        rw [hSe, h3, h.2 s (hSL hs)] at e2
        have hPS : ({p} ∪ {q} : Finset W) ⊆ S := by
          intro w hw
          rw [Finset.mem_union, Finset.mem_singleton, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl <;> assumption
        have hge := ep_cut_ge_two α β L hb hconn ({p} ∪ {q}) (hPS.trans hSL)
          ⟨p, Finset.mem_union_left _ (Finset.mem_singleton_self p)⟩
          (fun h' => hrS (hPS (h' ▸ hr)))
        have hne2 : (epCut α β ({p} ∪ {q} : Finset W)).card ≠ 2 := by
          intro hc2
          obtain ⟨k1, k2, k3⟩ := ep_decomp_insert α β L r 𝒮 hdec hr S ({p} ∪ {q})
            (Finset.mem_insert_of_mem hS) hPS (fun h' => hrS (hPS h')) (Or.inl hc2)
            (fun D hD => by rw [hleaf] at hD; exact absurd hD (Finset.notMem_empty D))
            (by
              rw [hatom, Finset.inter_eq_right.mpr hPS, Finset.card_union_of_disjoint hd,
                Finset.card_singleton, Finset.card_singleton]
              omega)
            (by
              rw [hatom, if_neg hSneL]
              have : 0 < (S \ ({p} ∪ {q})).card := Finset.card_pos.mpr ⟨s, Finset.mem_sdiff.mpr
                ⟨hs, fun h' => Finset.disjoint_left.mp hd2 h' (Finset.mem_singleton_self s)⟩⟩
              omega)
          have := hmax _ k2 (k3 𝒴 href hAY)
          rw [Finset.card_insert_of_notMem k1] at this
          omega
        constructor <;> omega
      obtain ⟨p1, p2⟩ := hpair x y z hxS hyS hzS hxy hxz hyz hTmem
      obtain ⟨q1, q2⟩ := hpair y z x hyS hzS hxS hyz (Ne.symm hxy) (Ne.symm hxz)
        (fun w => by rw [hTmem]; tauto)
      obtain ⟨r1, r2⟩ := hpair x z y hxS hzS hyS hxz hxy (Ne.symm hyz)
        (fun w => by rw [hTmem]; tauto)
      have u1 := ep_btw_union_le α β {z} {x} {y}
      rw [ep_btw_comm α β {z} ({x} ∪ {y}), ep_btw_comm α β {z} {x}, ep_btw_comm α β {z} {y}] at u1
      have n1 : 1 ≤ (epBtw α β {x} {y}).card := by omega
      have n2 : 1 ≤ (epBtw α β {y} {z}).card := by omega
      have n3 : 1 ≤ (epBtw α β {x} {z}).card := by omega
      obtain ⟨exy, hexy⟩ := Finset.card_pos.mp n1
      obtain ⟨eyz, heyz⟩ := Finset.card_pos.mp n2
      obtain ⟨exz, hexz⟩ := Finset.card_pos.mp n3
      have hedge : ∀ (p q : W) (e : E), p ≠ q → e ∈ epBtw α β {p} {q} →
          ∀ w, epCross α β {w} e ↔ w = p ∨ w = q := by
        intro p q e hpq he w
        rw [mem_epBtw] at he
        simp only [Finset.mem_singleton] at he
        exact ep_edge_cross α β p q e hpq he w
      have ht : EpTriangle α β L x y z exy eyz exz :=
        ⟨hSL hxS, hSL hyS, hSL hzS, hxy, hyz, hxz, hedge x y exy hxy hexy,
          hedge y z eyz hyz heyz, fun w => by
            rw [hedge x z exz hxz hexz w]; exact or_comm⟩
      have hrel : ¬EpIrrelevant α β x y z := by
        intro hirr
        rcases hpr x y z exy eyz exz ht hirr with rfl | rfl | rfl
        · exact hrS hxS
        · exact hrS hyS
        · exact hrS hzS
      have hmeet := ep_relevant_meets α β L h hb hconn hbig 𝒴 hfam hcov x y z exy eyz exz ht hrel
      rw [← hSeq, Finset.not_disjoint_iff] at hmeet
      obtain ⟨w, hwS, hwU⟩ := hmeet
      obtain ⟨Y, hY, hwY⟩ := Finset.mem_biUnion.mp hwU
      rcases href Y hY with ⟨a1, a2⟩ | ⟨-, a2, -⟩
      · rcases hdec.1 S hS Y a1 with h' | h' | h'
        · by_cases hSYe : S = Y
          · exact hSY (hSYe ▸ hY)
          · obtain ⟨C, hC, -⟩ := ep_child_above 𝒮 Y S hS
              (Finset.ssubset_iff_subset_ne.mpr ⟨h', hSYe⟩)
            rw [a2] at hC; exact absurd hC (Finset.notMem_empty C)
        · by_cases hSYe : Y = S
          · exact hSY (hSYe ▸ hY)
          · obtain ⟨C, hC, -⟩ := ep_child_above 𝒮 S Y a1
              (Finset.ssubset_iff_subset_ne.mpr ⟨h', hSYe⟩)
            rw [hleaf] at hC; exact absurd hC (Finset.notMem_empty C)
        · exact Finset.disjoint_left.mp h' hwS hwY
      · rw [a2] at hwY
        exact ((mem_epAtom 𝒮 L w).mp hwY).2 S hS
          (Finset.ssubset_iff_subset_ne.mpr ⟨hSL, hSneL⟩) hwS

open Classical in
/-- A foliage with root `r`: pairwise disjoint burls inside `L` avoiding `r`. -/
def EpFol {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (r : W)
    (𝒳 : Finset (Finset W)) : Prop :=
  (∀ X ∈ 𝒳, X ⊆ L ∧ r ∉ X ∧ EpBurl α β X) ∧ ∀ X ∈ 𝒳, ∀ X' ∈ 𝒳, X ≠ X' → Disjoint X X'

open Classical in
/-- The weight of a foliage: `β₁ = 196/995` for every twig, `β₂ = 98/995` for every other
burl. -/
noncomputable def epFw {W E : Type*} [Fintype E] (α β : E → W) (𝒳 : Finset (Finset W)) : ℝ :=
  ∑ X ∈ 𝒳, (if EpTwig α β X then (196 : ℝ) / 995 else 98 / 995)

open Classical in
lemma epFw_insert {W E : Type*} [Fintype E] (α β : E → W) (𝒳 : Finset (Finset W))
    (X : Finset W) (hX : X ∉ 𝒳) :
    epFw α β (insert X 𝒳) = (if EpTwig α β X then (196 : ℝ) / 995 else 98 / 995) + epFw α β 𝒳 := by
  unfold epFw
  rw [Finset.sum_insert hX]

open Classical in
/-- Dropping the members of a foliage that contain a given vertex loses at most `β₁`. -/
lemma ep_fol_drop {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (r : W)
    (𝒳 : Finset (Finset W)) (hfol : EpFol α β L r 𝒳) (v : W) :
    EpFol α β L r (𝒳.filter (fun X => v ∉ X)) ∧
      epFw α β 𝒳 - 196 / 995 ≤ epFw α β (𝒳.filter (fun X => v ∉ X)) := by
  refine ⟨⟨fun X hX => hfol.1 X (Finset.mem_of_mem_filter X hX), fun X hX X' hX' hne =>
    hfol.2 X (Finset.mem_of_mem_filter X hX) X' (Finset.mem_of_mem_filter X' hX') hne⟩, ?_⟩
  unfold epFw
  rw [← Finset.sum_filter_add_sum_filter_not 𝒳 (fun X => v ∉ X)]
  have hcard : (𝒳.filter (fun X => ¬v ∉ X)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro X hX X' hX'
    rw [Finset.mem_filter, not_not] at hX hX'
    by_contra hne
    exact Finset.disjoint_left.mp (hfol.2 X hX.1 X' hX'.1 hne) hX.2 hX'.2
  have hle : ∑ X ∈ 𝒳.filter (fun X => ¬v ∉ X),
      (if EpTwig α β X then (196 : ℝ) / 995 else 98 / 995) ≤ 196 / 995 := by
    calc _ ≤ ∑ X ∈ 𝒳.filter (fun X => ¬v ∉ X), (196 : ℝ) / 995 :=
          Finset.sum_le_sum (fun X _ => by split_ifs <;> norm_num)
      _ = ((𝒳.filter (fun X => ¬v ∉ X)).card : ℝ) * (196 / 995) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 1 * (196 / 995) := by
          apply mul_le_mul_of_nonneg_right _ (by norm_num)
          exact_mod_cast hcard
      _ = 196 / 995 := one_mul _
  linarith

open Classical in
/-- A foliage of a 3-cut contraction whose members avoid the new vertex is a foliage of the
original multigraph of the same weight, disjoint from the contracted set. -/
lemma ep_fol_lift_eq {W E : Type*} [Fintype E] (α β : E → W) (L X : Finset W) (x₀ x₁ r : W)
    (h : EpCubicD α β L) (hXL : X ⊆ L) (hx₀ : x₀ ∈ X) (hx₁ : x₁ ∈ X)
    (𝒳 : Finset (Finset W))
    (hfol : EpFol (epConA α β X x₀ x₁) (epConB α β X x₀ x₁) (epL' L X x₀) r 𝒳)
    (havoid : ∀ Z ∈ 𝒳, x₀ ∉ Z) :
    EpFol α β L r 𝒳 ∧ (∀ Z ∈ 𝒳, ∀ w, w ∈ Z → w ∉ X) ∧
      epFw α β 𝒳 = epFw (epConA α β X x₀ x₁) (epConB α β X x₀ x₁) 𝒳 := by
  have hZ : ∀ Z ∈ 𝒳, Z ⊆ L ∧ ∀ w, w ∈ Z → w ∉ X := by
    intro Z hZ
    have hsub := (hfol.1 Z hZ).1
    have key : ∀ w, w ∈ Z → w ∈ L ∧ w ∉ X := by
      intro w hw
      have := hsub hw
      unfold epL' at this
      rcases Finset.mem_insert.mp this with h' | h'
      · exact absurd (h' ▸ hw) (havoid Z hZ)
      · exact Finset.mem_sdiff.mp h'
    exact ⟨fun w hw => (key w hw).1, fun w hw => (key w hw).2⟩
  have hb : ∀ Z ∈ 𝒳, EpBurl α β Z ∧ (epCut α β Z).card =
      (epCut (epConA α β X x₀ x₁) (epConB α β X x₀ x₁) Z).card := fun Z hZ' =>
    epCon_burl α β L X Z x₀ x₁ h hXL hx₀ hx₁ (hZ Z hZ').1 (hZ Z hZ').2 (hfol.1 Z hZ').2.2
  refine ⟨⟨fun Z hZ' => ⟨(hZ Z hZ').1, (hfol.1 Z hZ').2.1, (hb Z hZ').1⟩, hfol.2⟩,
    fun Z hZ' => (hZ Z hZ').2, ?_⟩
  unfold epFw
  refine Finset.sum_congr rfl fun Z hZ' => ?_
  have : EpTwig α β Z ↔ EpTwig (epConA α β X x₀ x₁) (epConB α β X x₀ x₁) Z := by
    unfold EpTwig; rw [(hb Z hZ').2]
  by_cases ht : EpTwig α β Z
  · rw [if_pos ht, if_pos (this.mp ht)]
  · rw [if_neg ht, if_neg (fun h' => ht (this.mpr h'))]

set_option maxHeartbeats 3200000 in
open Classical in
/-- **Contraction step keeping the multigraph pruned away from the root.** For a set `M`
with a cut of size three not containing the root there is a multigraph reachable by
cut-contractions, with `|L| − |M| + 1` or `|L| − |M| − 1` vertices, again pruned away from the
root, whose foliages lift to foliages avoiding `M` with a loss of at most `β₁`. -/
theorem ep_prune_step {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (r : W)
    (h : EpCubicD α β L) (hb : EpBridgeless α β L) (hconn : EpConnected α β L) (hr : r ∈ L)
    (hpr : EpPrunedAt α β L r) (M : Finset W) (hML : M ⊆ L) (hrM : r ∉ M)
    (hM3 : (epCut α β M).card = 3) (hM2 : 2 ≤ M.card) (hbig : M.card + 4 ≤ L.card) :
    ∃ (α₁ β₁ : E → W) (L₁ : Finset W), EpReach α β L α₁ β₁ L₁ ∧ r ∈ L₁ ∧
      EpPrunedAt α₁ β₁ L₁ r ∧ L.card ≤ L₁.card + M.card + 1 ∧ L₁.card < L.card ∧
      ∀ 𝒳₁, EpFol α₁ β₁ L₁ r 𝒳₁ → ∃ 𝒳, EpFol α β L r 𝒳 ∧ (∀ Z ∈ 𝒳, ∀ w, w ∈ Z → w ∉ M) ∧
        epFw α₁ β₁ 𝒳₁ - 196 / 995 ≤ epFw α β 𝒳 := by
  obtain ⟨m₀, hm₀, m₁, hm₁, hm⟩ := Finset.one_lt_card.mp (by omega : 1 < M.card)
  have hstep : EpStep α β L (epConA α β M m₀ m₁) (epConB α β M m₀ m₁) (epL' L M m₀) :=
    Or.inl ⟨M, m₀, m₁, hML, hm₀, hm₁, hm.symm, hM3, rfl, rfl, rfl⟩
  obtain ⟨hH, hbH, hconnH, -, -⟩ := hstep.preserves h hb hconn
  have hcardH : (epL' L M m₀).card + M.card = L.card + 1 := by
    have e1 := Finset.card_sdiff_add_card_eq_card hML
    have e2 : (epL' L M m₀).card = (L \ M).card + 1 :=
      Finset.card_insert_of_notMem (fun h' => (Finset.mem_sdiff.mp h').2 hm₀)
    omega
  have hrH : r ∈ epL' L M m₀ := by
    unfold epL'; exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨hr, hrM⟩)
  have hrm₀ : r ≠ m₀ := fun h' => hrM (h' ▸ hm₀)
  -- irrelevant triangles of the contraction away from the root contain the new vertex
  have hclaim : ∀ p q s e1 e2 e3,
      EpTriangle (epConA α β M m₀ m₁) (epConB α β M m₀ m₁) (epL' L M m₀) p q s e1 e2 e3 →
      EpIrrelevant (epConA α β M m₀ m₁) (epConB α β M m₀ m₁) p q s →
      p ≠ r → q ≠ r → s ≠ r → p = m₀ ∨ q = m₀ ∨ s = m₀ := by
    intro p q s e1 e2 e3 ht hirr hp hq hs
    by_contra hcon
    push_neg at hcon
    obtain ⟨ht', hpM, hqM, hsM⟩ := epCon_triangle_back α β L M m₀ m₁ hm₀ hm₁ p q s e1 e2 e3 ht
      hcon.1 hcon.2.1 hcon.2.2
    by_cases hirr' : EpIrrelevant α β p q s
    · rcases hpr p q s e1 e2 e3 ht' hirr' with h' | h' | h'
      · exact hp h'
      · exact hq h'
      · exact hs h'
    · exact epCon_relevant α β L M m₀ m₁ h hm₀ p q s e1 e2 e3 ht' hpM hqM hsM hirr' hirr
  by_cases hprH : EpPrunedAt (epConA α β M m₀ m₁) (epConB α β M m₀ m₁) (epL' L M m₀) r
  · refine ⟨epConA α β M m₀ m₁, epConB α β M m₀ m₁, epL' L M m₀,
      Relation.ReflTransGen.single hstep, hrH, hprH, by omega, by omega, fun 𝒳₁ hfol => ?_⟩
    obtain ⟨d1, d2⟩ := ep_fol_drop _ _ _ r 𝒳₁ hfol m₀
    obtain ⟨l1, l2, l3⟩ := ep_fol_lift_eq α β L M m₀ m₁ r h hML hm₀ hm₁ _ d1
      (fun Z hZ => (Finset.mem_filter.mp hZ).2)
    exact ⟨_, l1, l2, by rw [l3]; exact d2⟩
  · unfold EpPrunedAt at hprH
    push_neg at hprH
    obtain ⟨x, y, z, exy, eyz, ezx, ht, hirr, hxr, hyr, hzr⟩ := hprH
    have hm₀T : m₀ ∈ ({x, y, z} : Finset W) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases hclaim x y z exy eyz ezx ht hirr hxr hyr hzr with h' | h' | h'
      · exact Or.inl h'.symm
      · exact Or.inr (Or.inl h'.symm)
      · exact Or.inr (Or.inr h'.symm)
    have h5 : 5 ≤ (epL' L M m₀).card := by omega
    obtain ⟨hTL, hT3, hTcut⟩ := ep_triangle_cut _ _ _ hH hbH hconnH h5 x y z exy eyz ezx ht
    have hxT : x ∈ ({x, y, z} : Finset W) := Finset.mem_insert_self _ _
    have hyT : y ∈ ({x, y, z} : Finset W) :=
      Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    have hxy : x ≠ y := ht.2.2.2.1
    have hstep2 : EpStep (epConA α β M m₀ m₁) (epConB α β M m₀ m₁) (epL' L M m₀)
        (epConA (epConA α β M m₀ m₁) (epConB α β M m₀ m₁) ({x, y, z} : Finset W) x y)
        (epConB (epConA α β M m₀ m₁) (epConB α β M m₀ m₁) ({x, y, z} : Finset W) x y)
        (epL' (epL' L M m₀) ({x, y, z} : Finset W) x) :=
      Or.inl ⟨_, x, y, hTL, hxT, hyT, hxy.symm, hTcut, rfl, rfl, rfl⟩
    have hreach2 : EpReach (epConA α β M m₀ m₁) (epConB α β M m₀ m₁) (epL' L M m₀)
        (epConA (epConA α β M m₀ m₁) (epConB α β M m₀ m₁) ({x, y, z} : Finset W) x y)
        (epConB (epConA α β M m₀ m₁) (epConB α β M m₀ m₁) ({x, y, z} : Finset W) x y)
        (epL' (epL' L M m₀) ({x, y, z} : Finset W) x) := Relation.ReflTransGen.single hstep2
    have hcard2 : (epL' (epL' L M m₀) ({x, y, z} : Finset W) x).card + 3 =
        (epL' L M m₀).card + 1 := by
      have e1 := Finset.card_sdiff_add_card_eq_card hTL
      have e2 : (epL' (epL' L M m₀) ({x, y, z} : Finset W) x).card =
          (epL' L M m₀ \ ({x, y, z} : Finset W)).card + 1 :=
        Finset.card_insert_of_notMem (fun h' => (Finset.mem_sdiff.mp h').2 hxT)
      omega
    have hrT : r ∉ ({x, y, z} : Finset W) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (h' | h' | h')
      · exact hxr h'.symm
      · exact hyr h'.symm
      · exact hzr h'.symm
    refine ⟨epConA (epConA α β M m₀ m₁) (epConB α β M m₀ m₁) ({x, y, z} : Finset W) x y,
      epConB (epConA α β M m₀ m₁) (epConB α β M m₀ m₁) ({x, y, z} : Finset W) x y,
      epL' (epL' L M m₀) ({x, y, z} : Finset W) x,
      Relation.ReflTransGen.head hstep hreach2,
      ?_, ?_, by omega, by omega, fun 𝒳₁ hfol => ?_⟩
    · unfold epL'
      exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨hrH, hrT⟩)
    · -- pruned away from the root
      intro p q s e1 e2 e3 ht₁ hirr₁
      by_contra hcon
      push_neg at hcon
      obtain ⟨a1, a2, a3, -⟩ := ep_tri_contract_triangle _ _ (epL' L M m₀) x y z hxy.symm hirr
        p q s e1 e2 e3 ht₁
      obtain ⟨ht₂, hpT, hqT, hsT⟩ := epCon_triangle_back _ _ (epL' L M m₀) ({x, y, z} : Finset W)
        x y hxT hyT p q s e1 e2 e3 ht₁ a1 a2 a3
      by_cases hirr₂ : EpIrrelevant (epConA α β M m₀ m₁) (epConB α β M m₀ m₁) p q s
      · rcases hclaim p q s e1 e2 e3 ht₂ hirr₂ hcon.1 hcon.2.1 hcon.2.2 with h' | h' | h'
        · exact hpT (h' ▸ hm₀T)
        · exact hqT (h' ▸ hm₀T)
        · exact hsT (h' ▸ hm₀T)
      · exact epCon_relevant _ _ (epL' L M m₀) ({x, y, z} : Finset W) x y hH hxT p q s e1 e2 e3
          ht₂ hpT hqT hsT hirr₂ hirr₁
    · obtain ⟨d1, d2⟩ := ep_fol_drop _ _ _ r 𝒳₁ hfol x
      obtain ⟨l1, l2, l3⟩ := ep_fol_lift_eq _ _ (epL' L M m₀) ({x, y, z} : Finset W) x y r hH hTL
        hxT hyT _ d1 (fun Z hZ => (Finset.mem_filter.mp hZ).2)
      obtain ⟨k1, k2, k3⟩ := ep_fol_lift_eq α β L M m₀ m₁ r h hML hm₀ hm₁ _ l1
        (fun Z hZ hm => l2 Z hZ m₀ hm hm₀T)
      exact ⟨_, k1, k2, by rw [k3, l3]; exact d2⟩

theorem EpHasCore.of_reach {W E : Type*} [Fintype E] {α β : E → W} {L : Finset W}
    {α' β' : E → W} {L' : Finset W} (hr : EpReach α β L α' β' L') (hc : EpHasCore α' β' L') :
    EpHasCore α β L := by
  obtain ⟨α'', β'', L'', hr', h4, h6⟩ := hc
  exact ⟨α'', β'', L'', Relation.ReflTransGen.trans hr hr', h4, h6⟩

open Classical in
/-- **Lemma 6.** Twigs are burls. -/
theorem ep_twig_burl {W E : Type*} [Fintype E] (α β : E → W) (L X : Finset W)
    (h : EpCubicD α β L) (hb : EpBridgeless α β L) (hconn : EpConnected α β L) (hXL : X ⊆ L)
    (y₁ : W) (hy₁ : y₁ ∈ L) (hy₁X : y₁ ∉ X) (ht : EpTwig α β X) : EpBurl α β X := by
  rcases ht with h2 | ⟨h3, h5⟩
  · obtain ⟨e, e', hee', hset⟩ := Finset.card_eq_two.mp h2
    have hcut : ∀ g, epCross α β X g ↔ g = e ∨ g = e' := by
      intro g; rw [← mem_epCut, hset, Finset.mem_insert, Finset.mem_singleton]
    exact ep_twig2_burl α β L X (L \ X) e e' y₁ h hb hXL (fun w => Finset.mem_sdiff)
      (Finset.mem_sdiff.mpr ⟨hy₁, hy₁X⟩) hee' hcut
  · exact ep_twig3_burl α β L X h hb hconn hXL h3 h5

open Classical in
/-- A set with a cut of size two or three not containing `r` lies in a set with a cut of size
three not containing `r`, with at most one more vertex. -/
lemma ep_member_three {W E : Type*} [Fintype E] (α β : E → W) (L N : Finset W) (r : W)
    (h : EpCubicD α β L) (hb : EpBridgeless α β L) (hNL : N ⊆ L) (hrN : r ∉ N)
    (hcut : (epCut α β N).card = 2 ∨ (epCut α β N).card = 3) :
    ∃ M, N ⊆ M ∧ M ⊆ L ∧ r ∉ M ∧ (epCut α β M).card = 3 ∧ M.card ≤ N.card + 1 := by
  rcases hcut with h2 | h3
  · obtain ⟨e, e', hee', hset⟩ := Finset.card_eq_two.mp h2
    have hc : ∀ g, epCross α β N g ↔ g = e ∨ g = e' := by
      intro g; rw [← mem_epCut, hset, Finset.mem_insert, Finset.mem_singleton]
    obtain ⟨a1, a2, a3, a4⟩ := ep_cut_insert_card α β L N h hb hNL e e' hee' hc e (Or.inl rfl)
    obtain ⟨b1, b2, b3, -⟩ := ep_cut_insert_card α β L N h hb hNL e e' hee' hc e' (Or.inr rfl)
    by_cases hra : r = epOut α β N e
    · refine ⟨insert (epOut α β N e') N, Finset.subset_insert _ _, ?_, ?_, b3, ?_⟩
      · exact Finset.insert_subset b1 hNL
      · rw [Finset.mem_insert]
        rintro (h' | h')
        · exact a4 e' (Or.inr rfl) (Ne.symm hee') (h'.symm.trans hra)
        · exact hrN h'
      · rw [Finset.card_insert_of_notMem b2]
    · refine ⟨insert (epOut α β N e) N, Finset.subset_insert _ _, ?_, ?_, a3, ?_⟩
      · exact Finset.insert_subset a1 hNL
      · rw [Finset.mem_insert]
        exact fun h' => h'.elim hra hrN
      · rw [Finset.card_insert_of_notMem a2]
  · exact ⟨N, Finset.Subset.refl _, hNL, hrN, h3, by omega⟩

open Classical in
/-- The union of two foliages whose members are pairwise disjoint. -/
lemma ep_fol_union {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (r : W)
    (𝒳 𝒯 : Finset (Finset W)) (h1 : EpFol α β L r 𝒳) (h2 : EpFol α β L r 𝒯)
    (hne : ∀ T ∈ 𝒯, T.Nonempty) (hd : ∀ Z ∈ 𝒳, ∀ T ∈ 𝒯, Disjoint Z T) :
    EpFol α β L r (𝒳 ∪ 𝒯) ∧ epFw α β (𝒳 ∪ 𝒯) = epFw α β 𝒳 + epFw α β 𝒯 := by
  have hdis : Disjoint 𝒳 𝒯 := by
    rw [Finset.disjoint_left]
    intro Z hZ hZ'
    obtain ⟨w, hw⟩ := hne Z hZ'
    exact Finset.disjoint_left.mp (hd Z hZ Z hZ') hw hw
  refine ⟨⟨fun X hX => ?_, fun X hX X' hX' hXX' => ?_⟩, ?_⟩
  · rcases Finset.mem_union.mp hX with h' | h'
    · exact h1.1 X h'
    · exact h2.1 X h'
  · rcases Finset.mem_union.mp hX with a | a <;> rcases Finset.mem_union.mp hX' with b | b
    · exact h1.2 X a X' b hXX'
    · exact hd X a X' b
    · exact (hd X' b X a).symm
    · exact h2.2 X a X' b hXX'
  · unfold epFw
    exact Finset.sum_union hdis

/-- `D` is the top of a chain with `j + 1` nodes ending in a leaf. -/
def EpChainTo {W : Type*} [DecidableEq W] (𝒮 : Finset (Finset W)) (D : Finset W) (j : ℕ) :
    Prop :=
  ∃ N : ℕ → Finset W, N 0 = D ∧ (∀ i, i ≤ j → N i ∈ 𝒮) ∧
    (∀ i, i < j → epChildren 𝒮 (N i) = {N (i + 1)}) ∧ epChildren 𝒮 (N j) = ∅

/-- A member all of whose descendants have at most one child is the top of a chain. -/
theorem ep_chain_exists {W : Type*} [DecidableEq W] (𝒮 : Finset (Finset W)) :
    ∀ (n : ℕ) (D : Finset W), D.card = n → D ∈ 𝒮 →
      (∀ S ∈ 𝒮, S ⊆ D → (epChildren 𝒮 S).card ≤ 1) → ∃ j, EpChainTo 𝒮 D j := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro D hn hD hone
    have h1 := hone D hD (Finset.Subset.refl _)
    by_cases h0 : (epChildren 𝒮 D).card = 0
    · exact ⟨0, fun _ => D, rfl, fun _ _ => hD, fun i hi => absurd hi (Nat.not_lt_zero i),
        Finset.card_eq_zero.mp h0⟩
    · obtain ⟨C, hC⟩ := Finset.card_eq_one.mp (by omega : (epChildren 𝒮 D).card = 1)
      have hCch : C ∈ epChildren 𝒮 D := by rw [hC]; exact Finset.mem_singleton_self C
      obtain ⟨hCS, hCD, -⟩ := (mem_epChildren 𝒮 D C).mp hCch
      obtain ⟨j, N, hN0, hNS, hNch, hNleaf⟩ := ih C.card (by rw [← hn]; exact Finset.card_lt_card hCD)
        C rfl hCS (fun S hS hSC => hone S hS (hSC.trans hCD.1))
      refine ⟨j + 1, fun i => Nat.rec D (fun i _ => N i) i, rfl, fun i hi => ?_, fun i hi => ?_,
        hNleaf⟩
      · cases i with
        | zero => exact hD
        | succ i => exact hNS i (by omega)
      · cases i with
        | zero => show epChildren 𝒮 D = {N 0}; rw [hN0]; exact hC
        | succ i => exact hNch i (by omega)

/-- Size of the top of a chain: at most `8 + 2j` if leaves have at most eight vertices and
atoms of nodes with one child at most two. -/
theorem ep_chain_size {W : Type*} [DecidableEq W] (𝒮 : Finset (Finset W))
    (hleaf : ∀ S ∈ 𝒮, epChildren 𝒮 S = ∅ → S.card ≤ 8)
    (hone : ∀ S ∈ 𝒮, ∀ C, epChildren 𝒮 S = {C} → (S \ C).card ≤ 2)
    (D : Finset W) (j : ℕ) (hch : EpChainTo 𝒮 D j) : D.card ≤ 8 + 2 * j := by
  obtain ⟨N, hN0, hNS, hNch, hNleaf⟩ := hch
  have key : ∀ d i, i + d = j → (N i).card ≤ 8 + 2 * d := by
    intro d
    induction d with
    | zero =>
      intro i hi
      have : i = j := by omega
      rw [this]
      exact hleaf _ (hNS j (le_refl j)) hNleaf
    | succ d ih =>
      intro i hi
      have h1 := hone _ (hNS i (by omega)) _ (hNch i (by omega))
      have h2 := ih (i + 1) (by omega)
      have hsub : N (i + 1) ⊆ N i := by
        have : N (i + 1) ∈ epChildren 𝒮 (N i) := by
          rw [hNch i (by omega)]; exact Finset.mem_singleton_self _
        exact ((mem_epChildren 𝒮 (N i) _).mp this).2.1.1
      have h3 := Finset.card_sdiff_add_card_eq_card hsub
      omega
  rw [← hN0]
  exact key j 0 (by omega)

/-- The leaf of a chain is a member inside its top. -/
lemma ep_chain_leaf {W : Type*} [DecidableEq W] (𝒮 : Finset (Finset W)) (D : Finset W)
    (j : ℕ) (hch : EpChainTo 𝒮 D j) :
    ∃ S ∈ 𝒮, S ⊆ D ∧ epChildren 𝒮 S = ∅ := by
  obtain ⟨N, hN0, hNS, hNch, hNleaf⟩ := hch
  refine ⟨N j, hNS j (le_refl j), ?_, hNleaf⟩
  have key : ∀ i, i ≤ j → N i ⊆ N 0 := by
    intro i
    induction i with
    | zero => exact fun _ => Finset.Subset.refl _
    | succ i ih =>
      intro hi
      have : N (i + 1) ∈ epChildren 𝒮 (N i) := by
        rw [hNch i (by omega)]; exact Finset.mem_singleton_self _
      exact ((mem_epChildren 𝒮 (N i) _).mp this).2.1.1.trans (ih (by omega))
  rw [← hN0]
  exact key j (le_refl j)

open Classical in
/-- A family of leaves that are twigs is a foliage of weight `β₁` times its size. -/
theorem ep_leaves_fol {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (r : W)
    (𝒮 𝒯 : Finset (Finset W)) (h : EpCubicD α β L) (hb : EpBridgeless α β L)
    (hconn : EpConnected α β L) (hr : r ∈ L) (hdec : EpDecomp α β L r 𝒮)
    (h𝒯 : ∀ T ∈ 𝒯, T ∈ 𝒮 ∧ epChildren 𝒮 T = ∅ ∧ EpTwig α β T) :
    EpFol α β L r 𝒯 ∧ epFw α β 𝒯 = (𝒯.card : ℝ) * (196 / 995) := by
  refine ⟨⟨fun T hT => ?_, fun T hT T' hT' hne => ?_⟩, ?_⟩
  · obtain ⟨a1, -, a3⟩ := h𝒯 T hT
    obtain ⟨b1, -, b3, -⟩ := hdec.2.1 T a1
    exact ⟨b1, b3, ep_twig_burl α β L T h hb hconn b1 r hr b3 a3⟩
  · obtain ⟨a1, a2, -⟩ := h𝒯 T hT
    obtain ⟨b1, b2, -⟩ := h𝒯 T' hT'
    rcases hdec.1 T a1 T' b1 with h' | h' | h'
    · obtain ⟨C, hC, -⟩ := ep_child_above 𝒮 T' T a1 (Finset.ssubset_iff_subset_ne.mpr ⟨h', hne⟩)
      rw [b2] at hC; exact absurd hC (Finset.notMem_empty C)
    · obtain ⟨C, hC, -⟩ := ep_child_above 𝒮 T T' b1
        (Finset.ssubset_iff_subset_ne.mpr ⟨h', hne.symm⟩)
      rw [a2] at hC; exact absurd hC (Finset.notMem_empty C)
    · exact h'
  · unfold epFw
    rw [Finset.sum_congr rfl (fun T hT => if_pos (h𝒯 T hT).2.2), Finset.sum_const, nsmul_eq_mul]

open Classical in
/-- Below a node all of whose proper descendants have at most one child, when all chains are
short: the node is small in terms of its atom and the number of its children, and there are at
least as many leaves below it as children. -/
lemma ep_branch_bounds {W : Type*} (𝒮 : Finset (Finset W)) (hlam : EpLaminar 𝒮)
    (hne : ∀ S ∈ 𝒮, S.Nonempty) (P : Finset W)
    (hbelow : ∀ S ∈ 𝒮, S ⊂ P → (epChildren 𝒮 S).card ≤ 1)
    (hchain : ∀ D j, EpChainTo 𝒮 D j → j ≤ 40)
    (hsize : ∀ D j, EpChainTo 𝒮 D j → D.card ≤ 8 + 2 * j) :
    P.card ≤ (epAtom 𝒮 P).card + 88 * (epChildren 𝒮 P).card ∧
      (epChildren 𝒮 P).card ≤ (𝒮.filter (fun S => S ⊂ P ∧ epChildren 𝒮 S = ∅)).card := by
  have hC : ∀ C, ∃ S, C ∈ epChildren 𝒮 P →
      (C.card ≤ 88 ∧ S ∈ 𝒮 ∧ S ⊆ C ∧ epChildren 𝒮 S = ∅ ∧ C ⊂ P) := by
    intro C
    by_cases hCc : C ∈ epChildren 𝒮 P
    · obtain ⟨hCS, hCP, -⟩ := (mem_epChildren 𝒮 P C).mp hCc
      obtain ⟨j, hj⟩ := ep_chain_exists 𝒮 C.card C rfl hCS
        (fun S hS hSC => hbelow S hS (lt_of_le_of_lt hSC hCP))
      obtain ⟨S, hS, hSC, hSl⟩ := ep_chain_leaf 𝒮 C j hj
      have := hchain C j hj
      have := hsize C j hj
      exact ⟨S, fun _ => ⟨by omega, hS, hSC, hSl, hCP⟩⟩
    · exact ⟨C, fun h' => absurd h' hCc⟩
  choose f hf using hC
  constructor
  · have hU : (epChildren 𝒮 P).biUnion id ⊆ P := by
      intro w hw
      obtain ⟨C, hCc, hwC⟩ := Finset.mem_biUnion.mp hw
      exact (hf C hCc).2.2.2.2.1 hwC
    have e1 := Finset.card_sdiff_add_card_eq_card hU
    rw [← ep_atom_children] at e1
    have e2 : ((epChildren 𝒮 P).biUnion id).card ≤ 88 * (epChildren 𝒮 P).card := by
      refine Finset.card_biUnion_le.trans ?_
      have := Finset.sum_le_card_nsmul (epChildren 𝒮 P) (fun C => (id C).card) 88
        (fun C hCc => (hf C hCc).1)
      rw [smul_eq_mul, mul_comm] at this
      exact this
    omega
  · refine Finset.card_le_card_of_injOn f (fun C hCc => ?_) (fun C hCc C' hCc' hff => ?_)
    · have hCc' : C ∈ epChildren 𝒮 P := hCc
      obtain ⟨-, a2, a3, a4, a5⟩ := hf C hCc'
      exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨a2, lt_of_le_of_lt a3 a5, a4⟩)
    · have h1 : C ∈ epChildren 𝒮 P := hCc
      have h2 : C' ∈ epChildren 𝒮 P := hCc'
      by_contra hneq
      obtain ⟨w, hw⟩ := hne _ (hf C h1).2.1
      have hd := ep_children_disjoint 𝒮 hlam P C C' h1 h2 hneq
      exact Finset.disjoint_left.mp hd ((hf C h1).2.2.1 hw) ((hf C' h2).2.2.1 (hff ▸ hw))

set_option maxHeartbeats 6400000 in
open Classical in
/-- **Lemma 11 (intrinsic form).** A cubic bridgeless connected multigraph without a core,
with at least six vertices and pruned away from `r`, has a foliage avoiding `r` of weight at
least `α |L| + β₂`, where `α = 1/995` and `β₂ = 98/995`. -/
theorem ep_lemma11 {W E : Type*} [Fintype E] : ∀ (n : ℕ) (α β : E → W) (L : Finset W) (r : W),
    L.card = n → EpCubicD α β L → EpBridgeless α β L → EpConnected α β L → r ∈ L →
    ¬EpHasCore α β L → EpPrunedAt α β L r → 6 ≤ L.card →
    ∃ 𝒳, EpFol α β L r 𝒳 ∧ (L.card : ℝ) / 995 + 98 / 995 ≤ epFw α β 𝒳 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro α β L r hn h hb hconn hr hnc hpr h6
    by_cases hsmall : L.card ≤ 98
    · -- the complement of the root is a twig
      have hcut : (epCut α β (L \ {r})).card = 3 := by
        have : epCut α β (L \ {r}) = epCut α β {r} := by
          ext g; rw [mem_epCut, mem_epCut]
          exact epD_cross_compl α β L {r} (L \ {r}) h (fun w => Finset.mem_sdiff) g
        rw [this]; exact h.2 r hr
      have hcard : (L \ {r}).card + 1 = L.card := by
        have := Finset.card_sdiff_add_card_eq_card (Finset.singleton_subset_iff.mpr hr)
        rw [Finset.card_singleton] at this
        exact this
      have htw : EpTwig α β (L \ {r}) := Or.inr ⟨hcut, by omega⟩
      have hrX : r ∉ L \ {r} := fun h' => (Finset.mem_sdiff.mp h').2 (Finset.mem_singleton_self r)
      refine ⟨{L \ {r}}, ⟨fun X hX => ?_, fun X hX X' hX' hne => ?_⟩, ?_⟩
      · rw [Finset.mem_singleton.mp hX]
        exact ⟨Finset.sdiff_subset, hrX,
          ep_twig_burl α β L _ h hb hconn Finset.sdiff_subset r hr hrX htw⟩
      · exact absurd ((Finset.mem_singleton.mp hX).trans (Finset.mem_singleton.mp hX').symm) hne
      · unfold epFw
        rw [Finset.sum_singleton, if_pos htw]
        have : (L.card : ℝ) ≤ 98 := by exact_mod_cast hsmall
        linarith
    · push_neg at hsmall
      have h4 : ¬EpCyc4 α β L := fun h4 => hnc ⟨α, β, L, Relation.ReflTransGen.refl, h4, by omega⟩
      obtain ⟨𝒴, hfam, hcov⟩ := ep_twigFam_exists_max α β L
      obtain ⟨𝒮, hdec, href, hmax⟩ :=
        ep_twig_decomp_exists α β L r h hb hconn hr h4 (by omega) 𝒴 hfam
      have F1 : ∀ S ∈ 𝒮, epChildren 𝒮 S = ∅ → EpTwig α β S ∧ S.card ≤ 8 := fun S hS hl =>
        ep_leaf_twig α β L r 𝒮 𝒴 h hb hconn hr (by omega) hfam hcov hdec href hmax hnc hpr S hS hl
      have F2 : ∀ S ∈ 𝒮, ∀ C, epChildren 𝒮 S = {C} → (S \ C).card ≤ 2 := fun S hS C hch =>
        (ep_deg2_atom_card α β L r 𝒮 𝒴 h hb hconn hr hdec href hmax hnc S C hS hch).2.1
      have hsize : ∀ D j, EpChainTo 𝒮 D j → D.card ≤ 8 + 2 * j :=
        ep_chain_size 𝒮 (fun S hS hl => (F1 S hS hl).2) F2
      have hSne : ∀ S ∈ 𝒮, S.Nonempty := fun S hS => (hdec.2.1 S hS).2.1
      -- one step of the induction: contract a set `M` and add a foliage inside `M`
      have hstep : ∀ (M : Finset W) (𝒯 : Finset (Finset W)), M ⊆ L → r ∉ M →
          (epCut α β M).card = 3 → 2 ≤ M.card → M.card + 7 ≤ L.card → EpFol α β L r 𝒯 →
          (∀ T ∈ 𝒯, T.Nonempty ∧ T ⊆ M) →
          ∃ 𝒳, EpFol α β L r 𝒳 ∧
            ((L.card : ℝ) - M.card - 1) / 995 + 98 / 995 - 196 / 995 + epFw α β 𝒯 ≤
              epFw α β 𝒳 := by
        intro M 𝒯 hML hrM hM3 hM2 hMbig h𝒯 h𝒯M
        obtain ⟨α₁, β₁, L₁, hreach, hr₁, hpr₁, hc1, hc2, hlift⟩ :=
          ep_prune_step α β L r h hb hconn hr hpr M hML hrM hM3 hM2 (by omega)
        obtain ⟨h₁, hb₁, hconn₁, -⟩ := hreach.preserves h hb hconn
        obtain ⟨𝒳₁, hfol₁, hw₁⟩ := ih L₁.card (by omega) α₁ β₁ L₁ r rfl h₁ hb₁ hconn₁ hr₁
          (fun hc => hnc (EpHasCore.of_reach hreach hc)) hpr₁ (by omega)
        obtain ⟨𝒳, hfol, havoid, hw⟩ := hlift 𝒳₁ hfol₁
        obtain ⟨u1, u2⟩ := ep_fol_union α β L r 𝒳 𝒯 hfol h𝒯 (fun T hT => (h𝒯M T hT).1)
          (fun Z hZ T hT => by
            rw [Finset.disjoint_left]
            exact fun w hw hw' => havoid Z hZ w hw ((h𝒯M T hT).2 hw'))
        refine ⟨𝒳 ∪ 𝒯, u1, ?_⟩
        rw [u2]
        have c1 : (L.card : ℝ) ≤ L₁.card + M.card + 1 := by exact_mod_cast hc1
        linarith
      by_cases hA : ∃ D j, EpChainTo 𝒮 D j ∧ 41 ≤ j
      · -- Case A: a long chain
        obtain ⟨D, j, ⟨N, hN0, hNS, hNch, hNleaf⟩, hj⟩ := hA
        obtain ⟨N', hN'⟩ : ∃ N' : ℕ → Finset W, ∀ i, N' i = N (i + (j - 41)) :=
          ⟨_, fun _ => rfl⟩
        have hNS' : ∀ i, i ≤ 41 → N' i ∈ 𝒮 := fun i hi => by
          rw [hN']; exact hNS _ (by omega)
        have hNch' : ∀ i, i < 41 → epChildren 𝒮 (N' i) = {N' (i + 1)} := by
          intro i hi
          rw [hN', hN', hNch _ (by omega)]
          have : i + (j - 41) + 1 = i + 1 + (j - 41) := by omega
          rw [this]
        have hNleaf' : epChildren 𝒮 (N' 41) = ∅ := by
          rw [hN']
          have : 41 + (j - 41) = j := by omega
          rw [this]; exact hNleaf
        have hstrict : ∀ i, i < 41 → N' (i + 1) ⊂ N' i := by
          intro i hi
          have : N' (i + 1) ∈ epChildren 𝒮 (N' i) := by
            rw [hNch' i hi]; exact Finset.mem_singleton_self _
          exact ((mem_epChildren 𝒮 (N' i) _).mp this).2.1
        have hmono : ∀ i, i ≤ 41 → N' i ⊆ N' 0 := by
          intro i
          induction i with
          | zero => exact fun _ => Finset.Subset.refl _
          | succ i ihi => exact fun hi => (hstrict i (by omega)).1.trans (ihi (by omega))
        have hburl := ep_chain_burl α β L r 𝒮 𝒴 h hb hconn hr hdec href hmax hnc N' hNS' hNch'
        obtain ⟨htw, -⟩ := F1 (N' 41) (hNS' 41 (le_refl _)) hNleaf'
        have hD90 : (N' 0).card ≤ 90 := by
          have := hsize (N' 0) 41 ⟨N', rfl, hNS', hNch', hNleaf'⟩
          omega
        obtain ⟨hN0L, hN0ne, hrN0, hN0cut⟩ := hdec.2.1 (N' 0) (hNS' 0 (by omega))
        obtain ⟨hN41L, hN41ne, hrN41, -⟩ := hdec.2.1 (N' 41) (hNS' 41 (le_refl _))
        obtain ⟨M, hNM, hML, hrM, hM3, hMcard⟩ :=
          ep_member_three α β L (N' 0) r h hb hN0L hrN0 hN0cut
        obtain ⟨w₀, hw₀, hw₀'⟩ := Finset.exists_of_ssubset (hstrict 0 (by omega))
        have hw₀41 : w₀ ∉ N' 41 := fun h' => by
          have s1 : N' 41 ⊆ N' 1 := by
            have key : ∀ i, 1 ≤ i → i ≤ 41 → N' i ⊆ N' 1 := by
              intro i hi
              induction i, hi using Nat.le_induction with
              | base => exact fun _ => Finset.Subset.refl _
              | succ i hi' ihi => exact fun hi'' => (hstrict i (by omega)).1.trans (ihi (by omega))
            exact key 41 (by omega) (le_refl _)
          exact hw₀' (s1 h')
        have hBne : (N' 0 \ N' 41).Nonempty := ⟨w₀, Finset.mem_sdiff.mpr ⟨hw₀, hw₀41⟩⟩
        obtain ⟨w₁, hw₁⟩ := hN41ne
        have hM2 : 2 ≤ M.card := by
          have : ({w₀, w₁} : Finset W) ⊆ M := by
            intro w hw
            rcases Finset.mem_insert.mp hw with rfl | hw
            · exact hNM hw₀
            · rw [Finset.mem_singleton.mp hw]; exact hNM (hmono 41 (le_refl _) hw₁)
          have := Finset.card_le_card this
          rw [Finset.card_pair (fun h' : w₀ = w₁ => hw₀41 (by rw [h']; exact hw₁))] at this
          exact this
        -- the twig and the burl
        have hBsub : N' 0 \ N' 41 ⊆ L := Finset.sdiff_subset.trans hN0L
        have hneTB : N' 41 ≠ N' 0 \ N' 41 := fun h' =>
          (Finset.mem_sdiff.mp (h' ▸ hw₁ : w₁ ∈ N' 0 \ N' 41)).2 hw₁
        have h𝒯 : EpFol α β L r (insert (N' 41) {N' 0 \ N' 41}) := by
          refine ⟨fun X hX => ?_, fun X hX X' hX' hne => ?_⟩
          · rcases Finset.mem_insert.mp hX with rfl | hX
            · exact ⟨hN41L, hrN41, ep_twig_burl α β L _ h hb hconn hN41L r hr hrN41 htw⟩
            · rw [Finset.mem_singleton.mp hX]
              exact ⟨hBsub, fun h' => hrN0 (Finset.mem_sdiff.mp h').1, hburl⟩
          · rcases Finset.mem_insert.mp hX with rfl | hX <;>
              rcases Finset.mem_insert.mp hX' with rfl | hX'
            · exact absurd rfl hne
            · rw [Finset.mem_singleton.mp hX']; exact Finset.sdiff_disjoint.symm
            · rw [Finset.mem_singleton.mp hX]; exact Finset.sdiff_disjoint
            · exact absurd ((Finset.mem_singleton.mp hX).trans (Finset.mem_singleton.mp hX').symm) hne
        have hw𝒯 : (196 : ℝ) / 995 + 98 / 995 ≤ epFw α β (insert (N' 41) {N' 0 \ N' 41}) := by
          rw [epFw_insert α β _ _ (fun h' => hneTB (Finset.mem_singleton.mp h')), if_pos htw]
          unfold epFw
          rw [Finset.sum_singleton]
          split_ifs <;> norm_num
        obtain ⟨𝒳, hfol, hw⟩ := hstep M _ hML hrM hM3 hM2 (by omega) h𝒯 (fun T hT => by
          rcases Finset.mem_insert.mp hT with rfl | hT
          · exact ⟨⟨w₁, hw₁⟩, (hmono 41 (le_refl _)).trans hNM⟩
          · rw [Finset.mem_singleton.mp hT]
            exact ⟨hBne, Finset.sdiff_subset.trans hNM⟩)
        refine ⟨𝒳, hfol, ?_⟩
        have c1 : (M.card : ℝ) ≤ 91 := by exact_mod_cast (by omega : M.card ≤ 91)
        linarith
      · -- Case B: all chains are short
        push_neg at hA
        have hchain : ∀ D j, EpChainTo 𝒮 D j → j ≤ 40 := fun D j hc => by
          have := hA D j hc; omega
        by_cases hBr : ∃ S ∈ 𝒮, 2 ≤ (epChildren 𝒮 S).card
        · -- a lowest branching member
          obtain ⟨S₀, hS₀, hS₀2⟩ := hBr
          obtain ⟨Ss, hSs, hmin⟩ := Finset.exists_min_image
            (𝒮.filter (fun S => 2 ≤ (epChildren 𝒮 S).card)) Finset.card
            ⟨S₀, Finset.mem_filter.mpr ⟨hS₀, hS₀2⟩⟩
          obtain ⟨hSsS, hSs2⟩ := Finset.mem_filter.mp hSs
          have hbelow : ∀ S ∈ 𝒮, S ⊂ Ss → (epChildren 𝒮 S).card ≤ 1 := by
            intro S hS hSS
            by_contra hcon
            have := hmin S (Finset.mem_filter.mpr ⟨hS, by omega⟩)
            have := Finset.card_lt_card hSS
            omega
          obtain ⟨b1, b2⟩ := ep_branch_bounds 𝒮 hdec.1 hSne Ss hbelow hchain hsize
          obtain ⟨hSsL, hSsne, hrSs, hSscut⟩ := hdec.2.1 Ss hSsS
          have hatom5 : (epAtom 𝒮 Ss).card ≤ 5 := by
            by_cases hAne : (epAtom 𝒮 Ss).Nonempty
            · obtain ⟨C, hC⟩ := Finset.card_pos.mp (by omega : 0 < (epChildren 𝒮 Ss).card)
              have hAY := ep_atom_notMem_refined α β L r 𝒮 𝒴 hdec href Ss C hSsS hC hAne
              obtain ⟨α', β', L', newE, hreach, h4', -, -, hcard, -, -⟩ :=
                ep_max_decomp_hub α β L r 𝒮 𝒴 h hb hconn hr hdec href hmax Ss
                  (Finset.mem_insert_of_mem hSsS) hAne hAY
              by_contra hcon
              exact hnc ⟨α', β', L', hreach, h4', by omega⟩
            · rw [Finset.not_nonempty_iff_eq_empty.mp hAne, Finset.card_empty]; omega
          obtain ⟨M, hSM, hML, hrM, hM3, hMcard⟩ :=
            ep_member_three α β L Ss r h hb hSsL hrSs hSscut
          have h𝒯mem : ∀ T ∈ 𝒮.filter (fun S => S ⊂ Ss ∧ epChildren 𝒮 S = ∅),
              T ∈ 𝒮 ∧ epChildren 𝒮 T = ∅ ∧ EpTwig α β T := by
            intro T hT
            obtain ⟨t1, -, t3⟩ := Finset.mem_filter.mp hT
            exact ⟨t1, t3, (F1 T t1 t3).1⟩
          obtain ⟨f1, f2⟩ := ep_leaves_fol α β L r 𝒮 _ h hb hconn hr hdec h𝒯mem
          have hM2 : 2 ≤ M.card := by
            have : 2 ≤ Ss.card := by
              obtain ⟨C, C', hCC', hpair⟩ : ∃ C C', C ≠ C' ∧ C ∈ epChildren 𝒮 Ss ∧
                  C' ∈ epChildren 𝒮 Ss := by
                obtain ⟨C, hC, C', hC', hne⟩ := Finset.one_lt_card.mp (by omega :
                  1 < (epChildren 𝒮 Ss).card)
                exact ⟨C, C', hne, hC, hC'⟩
              obtain ⟨c, hc⟩ := hSne C ((mem_epChildren 𝒮 Ss C).mp hpair.1).1
              obtain ⟨c', hc'⟩ := hSne C' ((mem_epChildren 𝒮 Ss C').mp hpair.2).1
              have hd := ep_children_disjoint 𝒮 hdec.1 Ss C C' hpair.1 hpair.2 hCC'
              have hsub : ({c, c'} : Finset W) ⊆ Ss := by
                intro w hw
                rcases Finset.mem_insert.mp hw with rfl | hw
                · exact ((mem_epChildren 𝒮 Ss C).mp hpair.1).2.1.1 hc
                · rw [Finset.mem_singleton.mp hw]
                  exact ((mem_epChildren 𝒮 Ss C').mp hpair.2).2.1.1 hc'
              have := Finset.card_le_card hsub
              rw [Finset.card_pair (fun h' : c = c' => Finset.disjoint_left.mp hd hc (by rw [h']; exact hc'))] at this
              exact this
            have := Finset.card_le_card hSM
            omega
          by_cases hsz : M.card + 7 ≤ L.card
          · obtain ⟨𝒳, hfol, hw⟩ := hstep M _ hML hrM hM3 hM2 hsz f1 (fun T hT => by
              obtain ⟨t1, t2, -⟩ := Finset.mem_filter.mp hT
              exact ⟨hSne T t1, t2.1.trans hSM⟩)
            refine ⟨𝒳, hfol, ?_⟩
            rw [f2] at hw
            have c1 : (M.card : ℝ) + 203 ≤
                196 * ((𝒮.filter (fun S => S ⊂ Ss ∧ epChildren 𝒮 S = ∅)).card : ℝ) := by
              have : M.card + 203 ≤
                  196 * (𝒮.filter (fun S => S ⊂ Ss ∧ epChildren 𝒮 S = ∅)).card := by omega
              exact_mod_cast this
            linarith
          · refine ⟨_, f1, ?_⟩
            rw [f2]
            have c1 : (L.card : ℝ) + 98 ≤
                196 * ((𝒮.filter (fun S => S ⊂ Ss ∧ epChildren 𝒮 S = ∅)).card : ℝ) := by
              have : L.card + 98 ≤
                  196 * (𝒮.filter (fun S => S ⊂ Ss ∧ epChildren 𝒮 S = ∅)).card := by omega
              exact_mod_cast this
            linarith
        · -- no branching member: the root
          push_neg at hBr
          have hbelow : ∀ S ∈ 𝒮, S ⊂ L → (epChildren 𝒮 S).card ≤ 1 := fun S hS _ => by
            have := hBr S hS; omega
          obtain ⟨b1, b2⟩ := ep_branch_bounds 𝒮 hdec.1 hSne L hbelow hchain hsize
          have hatom8 : (epAtom 𝒮 L).card ≤ 8 := by
            by_cases hAY : epAtom 𝒮 L ∈ 𝒴
            · exact (hfam.1 _ hAY).2.facts.2.1
            · obtain ⟨α', β', L', newE, hreach, h4', -, -, hcard, -, -⟩ :=
                ep_max_decomp_hub α β L r 𝒮 𝒴 h hb hconn hr hdec href hmax L
                  (Finset.mem_insert_self _ _) ⟨r, hdec.root_mem hr⟩ hAY
              by_contra hcon
              exact hnc ⟨α', β', L', hreach, h4', by omega⟩
          have h𝒯mem : ∀ T ∈ 𝒮.filter (fun S => S ⊂ L ∧ epChildren 𝒮 S = ∅),
              T ∈ 𝒮 ∧ epChildren 𝒮 T = ∅ ∧ EpTwig α β T := by
            intro T hT
            obtain ⟨t1, -, t3⟩ := Finset.mem_filter.mp hT
            exact ⟨t1, t3, (F1 T t1 t3).1⟩
          obtain ⟨f1, f2⟩ := ep_leaves_fol α β L r 𝒮 _ h hb hconn hr hdec h𝒯mem
          refine ⟨_, f1, ?_⟩
          rw [f2]
          have c1 : (L.card : ℝ) + 98 ≤
              196 * ((𝒮.filter (fun S => S ⊂ L ∧ epChildren 𝒮 S = ∅)).card : ℝ) := by
            have : L.card + 98 ≤
                196 * (𝒮.filter (fun S => S ⊂ L ∧ epChildren 𝒮 S = ∅)).card := by omega
            exact_mod_cast this
          linarith

/-- **Corollary 12.** A pruned cubic bridgeless connected multigraph without a core, with at
least six vertices, has for every vertex `v` a foliage avoiding `v` of weight at least
`α |L| + β₂`. -/
theorem ep_cor12 {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (v : W)
    (h : EpCubicD α β L) (hb : EpBridgeless α β L) (hconn : EpConnected α β L) (hv : v ∈ L)
    (hnc : ¬EpHasCore α β L) (hpr : EpPruned α β L) (h6 : 6 ≤ L.card) :
    ∃ 𝒳, EpFol α β L v 𝒳 ∧ (L.card : ℝ) / 995 + 98 / 995 ≤ epFw α β 𝒳 :=
  ep_lemma11 L.card α β L v rfl h hb hconn hv hnc
    (fun x y z exy eyz ezx ht hirr => absurd hirr (hpr x y z exy eyz ezx ht)) h6

open Classical in
/-- **Lemma 11 (for a side of a cut of size three).** Let `G` be pruned and `X` a set with a
cut of size three such that the contraction of `X` has no core and at least six vertices. Then
`G` has a foliage outside `X` of weight at least `α (|L ∖ X| + 1) + β₂`. -/
theorem ep_lemma11_cut {W E : Type*} [Fintype E] (α β : E → W) (L X : Finset W) (x₀ x₁ : W)
    (h : EpCubicD α β L) (hb : EpBridgeless α β L) (hconn : EpConnected α β L)
    (hpr : EpPruned α β L) (hXL : X ⊆ L) (hx₀ : x₀ ∈ X) (hx₁ : x₁ ∈ X) (hne : x₁ ≠ x₀)
    (h3 : (epCut α β X).card = 3)
    (hnc : ¬EpHasCore (epConA α β X x₀ x₁) (epConB α β X x₀ x₁) (epL' L X x₀))
    (h6 : 6 ≤ (epL' L X x₀).card) :
    ∃ 𝒳, EpFol α β L x₀ 𝒳 ∧ (∀ Z ∈ 𝒳, ∀ w, w ∈ Z → w ∉ X) ∧
      ((epL' L X x₀).card : ℝ) / 995 + 98 / 995 ≤ epFw α β 𝒳 := by
  have hstep : EpStep α β L (epConA α β X x₀ x₁) (epConB α β X x₀ x₁) (epL' L X x₀) :=
    Or.inl ⟨X, x₀, x₁, hXL, hx₀, hx₁, hne, h3, rfl, rfl, rfl⟩
  obtain ⟨h', hb', hconn', -, -⟩ := hstep.preserves h hb hconn
  have hx₀L : x₀ ∈ epL' L X x₀ := by unfold epL'; exact Finset.mem_insert_self _ _
  have hpr' : EpPrunedAt (epConA α β X x₀ x₁) (epConB α β X x₀ x₁) (epL' L X x₀) x₀ := by
    intro p q s e1 e2 e3 ht hirr
    by_contra hcon
    push_neg at hcon
    obtain ⟨ht', hpX, hqX, hsX⟩ := epCon_triangle_back α β L X x₀ x₁ hx₀ hx₁ p q s e1 e2 e3 ht
      hcon.1 hcon.2.1 hcon.2.2
    exact epCon_relevant α β L X x₀ x₁ h hx₀ p q s e1 e2 e3 ht' hpX hqX hsX
      (hpr p q s e1 e2 e3 ht') hirr
  obtain ⟨𝒳, hfol, hw⟩ := ep_lemma11 _ _ _ _ x₀ rfl h' hb' hconn' hx₀L hnc hpr' h6
  obtain ⟨l1, l2, l3⟩ := ep_fol_lift_eq α β L X x₀ x₁ x₀ h hXL hx₀ hx₁ 𝒳 hfol
    (fun Z hZ => (hfol.1 Z hZ).2.1)
  exact ⟨𝒳, l1, l2, by rw [l3]; exact hw⟩

/-- A pair of adjacent vertices `p`, `q` with their edges: `a`, `c`, `m` at `p` and `b`, `d`,
`m` at `q`, where `m` joins `p` and `q` and `a`, `b`, `c`, `d` are four different edges leaving
`{p, q}`. -/
def EpPath4 {W E : Type*} (α β : E → W) (L : Finset W) (p q : W) (a b c d m : E) : Prop :=
  p ∈ L ∧ q ∈ L ∧ p ≠ q ∧
    (∀ g, epCross α β {p} g ↔ g = a ∨ g = c ∨ g = m) ∧
    (∀ g, epCross α β {q} g ↔ g = b ∨ g = d ∨ g = m) ∧
    a ≠ c ∧ a ≠ m ∧ c ≠ m ∧ b ≠ d ∧ b ≠ m ∧ d ≠ m ∧ a ≠ b ∧ a ≠ d ∧ c ≠ b ∧ c ≠ d

open Classical in
/-- Splitting along a path: first ends. The edge `a` becomes the new edge joining the outer
ends of `a` and `b`, the edge `c` the new edge joining the outer ends of `c` and `d`, and every
other edge at `p` or `q` becomes a dead loop at `p`. -/
noncomputable def epSpA {W E : Type*} (α β : E → W) (p q : W) (a b c d : E) : E → W :=
  fun g => if g = a then epOut α β {p, q} a else if g = c then epOut α β {p, q} c
    else if α g ∈ ({p, q} : Finset W) ∨ β g ∈ ({p, q} : Finset W) then p else α g

open Classical in
/-- See `epSpA`. Second ends. -/
noncomputable def epSpB {W E : Type*} (α β : E → W) (p q : W) (a b c d : E) : E → W :=
  fun g => if g = a then epOut α β {p, q} b else if g = c then epOut α β {p, q} d
    else if α g ∈ ({p, q} : Finset W) ∨ β g ∈ ({p, q} : Finset W) then p else β g

open Classical in
/-- Ends of the four edges leaving the pair. -/
lemma EpPath4.ends {W E : Type*} {α β : E → W} {L : Finset W} {p q : W} {a b c d m : E}
    (hp : EpPath4 α β L p q a b c d m) :
    (∀ g, (g = a ∨ g = c) → epOut α β {p, q} g ∉ ({p, q} : Finset W) ∧
      ((α g = p ∧ β g = epOut α β {p, q} g) ∨ (α g = epOut α β {p, q} g ∧ β g = p))) ∧
    (∀ g, (g = b ∨ g = d) → epOut α β {p, q} g ∉ ({p, q} : Finset W) ∧
      ((α g = q ∧ β g = epOut α β {p, q} g) ∨ (α g = epOut α β {p, q} g ∧ β g = q))) ∧
    ((α m = p ∧ β m = q) ∨ (α m = q ∧ β m = p)) := by
  obtain ⟨hpL, hqL, hpq, hsp, hsq, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ := hp
  have hmp := (hsp m).mpr (Or.inr (Or.inr rfl))
  have hmq := (hsq m).mpr (Or.inr (Or.inr rfl))
  rw [epCross_singleton] at hmp hmq
  have hm : (α m = p ∧ β m = q) ∨ (α m = q ∧ β m = p) := by
    rcases hmp with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases hmq with ⟨b1, b2⟩ | ⟨b1, b2⟩
    · exact absurd (a1.symm.trans b1) hpq
    · exact Or.inl ⟨a1, b2⟩
    · exact Or.inr ⟨b1, a2⟩
    · exact absurd (a2.symm.trans b2) hpq
  have key : ∀ (g : E) (s t : W), s ≠ t → epCross α β {s} g → ¬epCross α β {t} g →
      ({s, t} : Finset W) = {p, q} →
      epOut α β {p, q} g ∉ ({p, q} : Finset W) ∧
        ((α g = s ∧ β g = epOut α β {p, q} g) ∨ (α g = epOut α β {p, q} g ∧ β g = s)) := by
    intro g s t hst hs ht hset
    rw [epCross_singleton] at hs ht
    have hmem : ∀ w, w ∈ ({p, q} : Finset W) ↔ w = s ∨ w = t := by
      intro w; rw [← hset]; simp only [Finset.mem_insert, Finset.mem_singleton]
    unfold epOut
    rcases hs with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · have hb : β g ∉ ({p, q} : Finset W) := by
        rw [hmem]; rintro (h' | h')
        · exact a2 h'
        · exact ht (Or.inr ⟨fun h'' => hst (a1.symm.trans h''), h'⟩)
      rw [if_pos ((hmem _).mpr (Or.inl a1))]
      exact ⟨hb, Or.inl ⟨a1, rfl⟩⟩
    · have ha : α g ∉ ({p, q} : Finset W) := by
        rw [hmem]; rintro (h' | h')
        · exact a1 h'
        · exact ht (Or.inl ⟨h', fun h'' => hst (a2.symm.trans h'')⟩)
      rw [if_neg ha]
      exact ⟨ha, Or.inr ⟨rfl, a2⟩⟩
  refine ⟨fun g hg => ?_, fun g hg => ?_, hm⟩
  · refine key g p q hpq ((hsp g).mpr (hg.elim Or.inl (fun h' => Or.inr (Or.inl h')))) ?_ rfl
    rw [hsq]
    rcases hg with rfl | rfl
    · exact fun h' => h'.elim d7 (fun h'' => h''.elim d8 d2)
    · exact fun h' => h'.elim d9 (fun h'' => h''.elim d10 d3)
  · have hset : ({q, p} : Finset W) = {p, q} := by
      ext w; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    refine key g q p (Ne.symm hpq) ((hsq g).mpr (hg.elim Or.inl (fun h' => Or.inr (Or.inl h'))))
      ?_ hset
    rw [hsp]
    rcases hg with rfl | rfl
    · exact fun h' => h'.elim (fun h'' => d7 h''.symm)
        (fun h'' => h''.elim (fun h3 => d9 h3.symm) d5)
    · exact fun h' => h'.elim (fun h'' => d8 h''.symm)
        (fun h'' => h''.elim (fun h3 => d10 h3.symm) d6)

open Classical in
/-- The edges at `p` or `q` are exactly `a`, `b`, `c`, `d`, `m`. -/
lemma EpPath4.touch {W E : Type*} {α β : E → W} {L : Finset W} {p q : W} {a b c d m : E}
    (hp : EpPath4 α β L p q a b c d m) (hnl : ∀ g, α g ∈ L → α g ≠ β g) (hlive : ∀ g, β g ∈ L → α g ∈ L)
    (g : E) :
    (α g ∈ ({p, q} : Finset W) ∨ β g ∈ ({p, q} : Finset W)) ↔
      g = a ∨ g = b ∨ g = c ∨ g = d ∨ g = m := by
  obtain ⟨he1, he2, hm⟩ := hp.ends
  obtain ⟨hpL, hqL, hpq, hsp, hsq, -⟩ := hp
  have hmem : ∀ w, w ∈ ({p, q} : Finset W) ↔ w = p ∨ w = q := by
    intro w; simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h'
    have hgL : α g ∈ L := by
      rcases h' with h' | h'
      · rcases (hmem _).mp h' with e | e <;> rw [e] <;> assumption
      · apply hlive
        rcases (hmem _).mp h' with e | e <;> rw [e] <;> assumption
    have hne := hnl g hgL
    have hcr : epCross α β {p} g ∨ epCross α β {q} g := by
      rw [epCross_singleton, epCross_singleton]
      rcases h' with h' | h'
      · rcases (hmem _).mp h' with e | e
        · exact Or.inl (Or.inl ⟨e, fun h'' => hne (e.trans h''.symm)⟩)
        · exact Or.inr (Or.inl ⟨e, fun h'' => hne (e.trans h''.symm)⟩)
      · rcases (hmem _).mp h' with e | e
        · exact Or.inl (Or.inr ⟨fun h'' => hne (h''.trans e.symm), e⟩)
        · exact Or.inr (Or.inr ⟨fun h'' => hne (h''.trans e.symm), e⟩)
    rcases hcr with h'' | h''
    · rcases (hsp g).mp h'' with e | e | e
      · exact Or.inl e
      · exact Or.inr (Or.inr (Or.inl e))
      · exact Or.inr (Or.inr (Or.inr (Or.inr e)))
    · rcases (hsq g).mp h'' with e | e | e
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr (Or.inr (Or.inl e)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr e)))
  · rintro (rfl | rfl | rfl | rfl | rfl)
    · rcases (he1 g (Or.inl rfl)).2 with ⟨e, -⟩ | ⟨-, e⟩
      · exact Or.inl ((hmem _).mpr (Or.inl e))
      · exact Or.inr ((hmem _).mpr (Or.inl e))
    · rcases (he2 g (Or.inl rfl)).2 with ⟨e, -⟩ | ⟨-, e⟩
      · exact Or.inl ((hmem _).mpr (Or.inr e))
      · exact Or.inr ((hmem _).mpr (Or.inr e))
    · rcases (he1 g (Or.inr rfl)).2 with ⟨e, -⟩ | ⟨-, e⟩
      · exact Or.inl ((hmem _).mpr (Or.inl e))
      · exact Or.inr ((hmem _).mpr (Or.inl e))
    · rcases (he2 g (Or.inr rfl)).2 with ⟨e, -⟩ | ⟨-, e⟩
      · exact Or.inl ((hmem _).mpr (Or.inr e))
      · exact Or.inr ((hmem _).mpr (Or.inr e))
    · rcases hm with ⟨e, -⟩ | ⟨e, -⟩
      · exact Or.inl ((hmem _).mpr (Or.inl e))
      · exact Or.inl ((hmem _).mpr (Or.inr e))

/-- Merging two elements of a finite set into one does not change the cardinality when at most
one of them is present. -/
lemma ep_card_merge {E : Type*} [DecidableEq E] (S S' : Finset E) (a b : E) (hab : a ≠ b)
    (ha : a ∈ S' ↔ a ∈ S ∨ b ∈ S) (hb : b ∉ S') (hnot : ¬(a ∈ S ∧ b ∈ S))
    (hrest : ∀ g, g ≠ a → g ≠ b → (g ∈ S' ↔ g ∈ S)) : S'.card = S.card := by
  by_cases hbS : b ∈ S
  · have haS : a ∉ S := fun h' => hnot ⟨h', hbS⟩
    have : S' = insert a (S.erase b) := by
      ext g
      rw [Finset.mem_insert, Finset.mem_erase]
      by_cases hga : g = a
      · rw [hga]; exact ⟨fun _ => Or.inl rfl, fun _ => ha.mpr (Or.inr hbS)⟩
      · by_cases hgb : g = b
        · rw [hgb]; exact ⟨fun h' => absurd h' hb, fun h' => h'.elim (fun h'' => absurd h''.symm hab)
            (fun h'' => absurd rfl h''.1)⟩
        · rw [hrest g hga hgb]
          exact ⟨fun h' => Or.inr ⟨hgb, h'⟩, fun h' => h'.elim (fun h'' => absurd h'' hga) (·.2)⟩
    rw [this, Finset.card_insert_of_notMem (fun h' => haS (Finset.mem_of_mem_erase h')),
      Finset.card_erase_of_mem hbS]
    have := Finset.card_pos.mpr ⟨b, hbS⟩
    omega
  · have : S' = S := by
      ext g
      by_cases hga : g = a
      · rw [hga, ha]; exact ⟨fun h' => h'.elim id (fun h'' => absurd h'' hbS), Or.inl⟩
      · by_cases hgb : g = b
        · rw [hgb]; exact ⟨fun h' => absurd h' hb, fun h' => absurd h' hbS⟩
        · exact hrest g hga hgb
    rw [this]

open Classical in
/-- Crossing in the split multigraph, for vertex sets avoiding `p` and `q`. -/
lemma epSp_cross {W E : Type*} (α β : E → W) (p q : W) (a b c d : E) (hac : a ≠ c)
    (T' : Finset W) (hpT : p ∉ T') :
    (epCross (epSpA α β p q a b c d) (epSpB α β p q a b c d) T' a ↔
      (epOut α β {p, q} a ∈ T' ∧ epOut α β {p, q} b ∉ T') ∨
        (epOut α β {p, q} a ∉ T' ∧ epOut α β {p, q} b ∈ T')) ∧
    (epCross (epSpA α β p q a b c d) (epSpB α β p q a b c d) T' c ↔
      (epOut α β {p, q} c ∈ T' ∧ epOut α β {p, q} d ∉ T') ∨
        (epOut α β {p, q} c ∉ T' ∧ epOut α β {p, q} d ∈ T')) ∧
    (∀ g, g ≠ a → g ≠ c → (α g ∈ ({p, q} : Finset W) ∨ β g ∈ ({p, q} : Finset W)) →
      ¬epCross (epSpA α β p q a b c d) (epSpB α β p q a b c d) T' g) ∧
    (∀ g, g ≠ a → g ≠ c → ¬(α g ∈ ({p, q} : Finset W) ∨ β g ∈ ({p, q} : Finset W)) →
      (epCross (epSpA α β p q a b c d) (epSpB α β p q a b c d) T' g ↔ epCross α β T' g)) := by
  refine ⟨?_, ?_, fun g hga hgc ht => ?_, fun g hga hgc ht => ?_⟩
  · unfold epCross epSpA epSpB
    rw [if_pos rfl, if_pos rfl]
  · unfold epCross epSpA epSpB
    rw [if_neg hac.symm, if_neg hac.symm, if_pos rfl, if_pos rfl]
  · unfold epCross epSpA epSpB
    rw [if_neg hga, if_neg hga, if_neg hgc, if_neg hgc, if_pos ht, if_pos ht]
    tauto
  · unfold epCross epSpA epSpB
    rw [if_neg hga, if_neg hga, if_neg hgc, if_neg hgc, if_neg ht, if_neg ht]

set_option maxHeartbeats 3200000 in
open Classical in
/-- **Lemma 23(1), first part.** The split multigraph is cubic (with dead edges). -/
theorem epSp_cubic {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (p q : W)
    (a b c d m : E) (h : EpCubicD α β L) (hp : EpPath4 α β L p q a b c d m)
    (hab : epOut α β {p, q} a ≠ epOut α β {p, q} b)
    (hcd : epOut α β {p, q} c ≠ epOut α β {p, q} d) :
    EpCubicD (epSpA α β p q a b c d) (epSpB α β p q a b c d) (L \ {p, q}) := by
  obtain ⟨he1, he2, hm⟩ := hp.ends
  have hnl : ∀ g, α g ∈ L → α g ≠ β g := by
    intro g hg
    rcases h.1 g with h' | h'
    · exact h'.2.2
    · exact absurd hg h'.1
  have hlv : ∀ g, β g ∈ L → α g ∈ L := by
    intro g hg
    rcases h.1 g with h' | h'
    · exact h'.1
    · exact absurd (h'.2 ▸ hg) h'.1
  have htouch := hp.touch hnl hlv
  obtain ⟨hpL, hqL, hpq, hsp, hsq, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ := hp
  have hmem : ∀ w, w ∈ ({p, q} : Finset W) ↔ w = p ∨ w = q := by
    intro w; simp only [Finset.mem_insert, Finset.mem_singleton]
  -- the outer ends are vertices outside the pair
  have hout : ∀ g, (g = a ∨ g = b ∨ g = c ∨ g = d) → epOut α β {p, q} g ∈ L \ {p, q} := by
    intro g hg
    have key : ∀ s, s ∈ L → epOut α β {p, q} g ∉ ({p, q} : Finset W) →
        ((α g = s ∧ β g = epOut α β {p, q} g) ∨ (α g = epOut α β {p, q} g ∧ β g = s)) →
        epOut α β {p, q} g ∈ L \ {p, q} := by
      intro s hs hn hends
      refine Finset.mem_sdiff.mpr ⟨?_, hn⟩
      rcases h.1 g with ⟨l1, l2, -⟩ | ⟨l1, l2⟩
      · rcases hends with ⟨-, e2⟩ | ⟨e1, -⟩
        · exact e2 ▸ l2
        · exact e1 ▸ l1
      · rcases hends with ⟨e1, -⟩ | ⟨-, e2⟩
        · exact absurd (e1 ▸ hs) l1
        · exact absurd (e2 ▸ hs) (l2 ▸ l1)
    rcases hg with rfl | rfl | rfl | rfl
    · exact key p hpL (he1 _ (Or.inl rfl)).1 (he1 _ (Or.inl rfl)).2
    · exact key q hqL (he2 _ (Or.inl rfl)).1 (he2 _ (Or.inl rfl)).2
    · exact key p hpL (he1 _ (Or.inr rfl)).1 (he1 _ (Or.inr rfl)).2
    · exact key q hqL (he2 _ (Or.inr rfl)).1 (he2 _ (Or.inr rfl)).2
  have hpL' : p ∉ L \ ({p, q} : Finset W) := fun h' =>
    (Finset.mem_sdiff.mp h').2 ((hmem p).mpr (Or.inl rfl))
  constructor
  · intro g
    by_cases hga : g = a
    · left
      rw [hga]
      unfold epSpA epSpB
      rw [if_pos rfl, if_pos rfl]
      exact ⟨hout a (Or.inl rfl), hout b (Or.inr (Or.inl rfl)), hab⟩
    · by_cases hgc : g = c
      · left
        rw [hgc]
        unfold epSpA epSpB
        rw [if_neg d1.symm, if_neg d1.symm, if_pos rfl, if_pos rfl]
        exact ⟨hout c (Or.inr (Or.inr (Or.inl rfl))), hout d (Or.inr (Or.inr (Or.inr rfl))), hcd⟩
      · by_cases ht : α g ∈ ({p, q} : Finset W) ∨ β g ∈ ({p, q} : Finset W)
        · right
          unfold epSpA epSpB
          rw [if_neg hga, if_neg hga, if_neg hgc, if_neg hgc, if_pos ht, if_pos ht]
          exact ⟨hpL', rfl⟩
        · unfold epSpA epSpB
          rw [if_neg hga, if_neg hga, if_neg hgc, if_neg hgc, if_neg ht, if_neg ht]
          push_neg at ht
          rcases h.1 g with ⟨l1, l2, l3⟩ | ⟨l1, l2⟩
          · exact Or.inl ⟨Finset.mem_sdiff.mpr ⟨l1, ht.1⟩, Finset.mem_sdiff.mpr ⟨l2, ht.2⟩, l3⟩
          · exact Or.inr ⟨fun h' => l1 (Finset.mem_sdiff.mp h').1, l2⟩
  · intro v hv
    obtain ⟨hvL, hvpq⟩ := Finset.mem_sdiff.mp hv
    have hvp : v ≠ p := fun h' => hvpq ((hmem v).mpr (Or.inl h'))
    have hvq : v ≠ q := fun h' => hvpq ((hmem v).mpr (Or.inr h'))
    obtain ⟨c1, c2, c3, c4⟩ := epSp_cross α β p q a b c d d1 {v}
      (fun h' => hvp (Finset.mem_singleton.mp h').symm)
    simp only [Finset.mem_singleton] at c1 c2
    -- crossing of `{v}` by the five special edges in `G`
    have hcrout : ∀ g s, s ≠ v → epOut α β {p, q} g ∉ ({p, q} : Finset W) →
        ((α g = s ∧ β g = epOut α β {p, q} g) ∨ (α g = epOut α β {p, q} g ∧ β g = s)) →
        (epCross α β {v} g ↔ epOut α β {p, q} g = v) := by
      intro g s hs hn hends
      rw [epCross_singleton]
      rcases hends with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [e1, ← e2]
        exact ⟨fun h' => h'.elim (fun h'' => absurd h''.1 hs) (·.2), fun h' => Or.inr ⟨hs, h'⟩⟩
      · rw [e2, ← e1]
        exact ⟨fun h' => h'.elim (·.1) (fun h'' => absurd h''.2 hs), fun h' => Or.inl ⟨h', hs⟩⟩
    have Ca := hcrout a p hvp.symm (he1 _ (Or.inl rfl)).1 (he1 _ (Or.inl rfl)).2
    have Cc := hcrout c p hvp.symm (he1 _ (Or.inr rfl)).1 (he1 _ (Or.inr rfl)).2
    have Cb := hcrout b q hvq.symm (he2 _ (Or.inl rfl)).1 (he2 _ (Or.inl rfl)).2
    have Cd := hcrout d q hvq.symm (he2 _ (Or.inr rfl)).1 (he2 _ (Or.inr rfl)).2
    have Cm : ¬epCross α β {v} m := by
      rw [epCross_singleton]
      rcases hm with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
      · exact fun h' => h'.elim (fun h'' => hvp h''.1.symm) (fun h'' => hvq h''.2.symm)
      · exact fun h' => h'.elim (fun h'' => hvq h''.1.symm) (fun h'' => hvp h''.2.symm)
    -- intermediate set: merge `b` into `a`
    obtain ⟨S₁, hS₁⟩ : ∃ S₁ : Finset E, ∀ g, g ∈ S₁ ↔
        (if g = a then (a ∈ epCut α β {v} ∨ b ∈ epCut α β {v}) else
          if g = b then False else g ∈ epCut α β {v}) :=
      ⟨Finset.univ.filter (fun g => if g = a then (a ∈ epCut α β {v} ∨ b ∈ epCut α β {v}) else
          if g = b then False else g ∈ epCut α β {v}), fun g => by
        rw [Finset.mem_filter]; simp⟩
    have e1 : S₁.card = (epCut α β {v}).card := by
      refine ep_card_merge _ _ a b d7 ?_ ?_ ?_ ?_
      · rw [hS₁, if_pos rfl]
      · rw [hS₁, if_neg d7.symm, if_pos rfl]; exact fun h' => h'
      · rw [mem_epCut, mem_epCut, Ca, Cb]
        exact fun h' => hab (h'.1.trans h'.2.symm)
      · intro g hga hgb; rw [hS₁, if_neg hga, if_neg hgb]
    have e2 : (epCut (epSpA α β p q a b c d) (epSpB α β p q a b c d) {v}).card = S₁.card := by
      refine ep_card_merge _ _ c d d10 ?_ ?_ ?_ ?_
      · rw [mem_epCut, c2, hS₁, hS₁, if_neg d1.symm, if_neg d9, if_neg d8.symm, if_neg d4.symm,
          mem_epCut, mem_epCut, Cc, Cd]
        constructor
        · rintro (⟨h', -⟩ | ⟨-, h'⟩)
          · exact Or.inl h'
          · exact Or.inr h'
        · rintro (h' | h')
          · exact Or.inl ⟨h', fun h'' => hcd (h'.trans h''.symm)⟩
          · exact Or.inr ⟨fun h'' => hcd (h''.trans h'.symm), h'⟩
      · rw [mem_epCut]
        exact c3 d d8.symm d10.symm ((htouch d).mpr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      · rw [hS₁, hS₁, if_neg d1.symm, if_neg d9, if_neg d8.symm, if_neg d4.symm,
          mem_epCut, mem_epCut, Cc, Cd]
        exact fun h' => hcd (h'.1.trans h'.2.symm)
      · intro g hgc hgd
        rw [mem_epCut, hS₁]
        by_cases hga : g = a
        · rw [if_pos hga, hga, c1, mem_epCut, mem_epCut, Ca, Cb]
          constructor
          · rintro (⟨h', -⟩ | ⟨-, h'⟩)
            · exact Or.inl h'
            · exact Or.inr h'
          · rintro (h' | h')
            · exact Or.inl ⟨h', fun h'' => hab (h'.trans h''.symm)⟩
            · exact Or.inr ⟨fun h'' => hab (h''.trans h'.symm), h'⟩
        · rw [if_neg hga]
          by_cases hgb : g = b
          · rw [if_pos hgb, hgb]
            have := c3 b d7.symm d9.symm ((htouch b).mpr (Or.inr (Or.inl rfl)))
            exact ⟨fun h' => this h', fun h' => h'.elim⟩
          · rw [if_neg hgb, mem_epCut]
            by_cases ht : α g ∈ ({p, q} : Finset W) ∨ β g ∈ ({p, q} : Finset W)
            · have hgm : g = m := by
                rcases (htouch g).mp ht with e | e | e | e | e
                · exact absurd e hga
                · exact absurd e hgb
                · exact absurd e hgc
                · exact absurd e hgd
                · exact e
              rw [hgm]
              exact ⟨fun h' => absurd h' (c3 m d2.symm d3.symm ((htouch m).mpr
                (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))), fun h' => absurd h' Cm⟩
            · exact c4 g hga hgc ht
    rw [e2, e1]
    exact h.2 v hvL

lemma ep_card_two {E : Type*} [DecidableEq E] (S : Finset E) (c d : E) (hcd : c ≠ d) :
    S.card = ((S.erase c).erase d).card + (if c ∈ S then 1 else 0) + (if d ∈ S then 1 else 0) := by
  have hd : d ∈ S.erase c ↔ d ∈ S := by rw [Finset.mem_erase]; exact ⟨(·.2), fun h => ⟨hcd.symm, h⟩⟩
  by_cases h1 : c ∈ S <;> by_cases h2 : d ∈ S
  · rw [if_pos h1, if_pos h2, Finset.card_erase_of_mem (hd.mpr h2), Finset.card_erase_of_mem h1]
    have := Finset.card_pos.mpr ⟨c, h1⟩
    have : 0 < (S.erase c).card := Finset.card_pos.mpr ⟨d, hd.mpr h2⟩
    have e := Finset.card_erase_of_mem h1
    omega
  · rw [if_pos h1, if_neg h2, Finset.erase_eq_of_notMem (fun h' => h2 (hd.mp h')),
      Finset.card_erase_of_mem h1]
    have := Finset.card_pos.mpr ⟨c, h1⟩
    omega
  · rw [if_neg h1, if_pos h2, Finset.erase_eq_of_notMem h1, Finset.card_erase_of_mem h2]
    have := Finset.card_pos.mpr ⟨d, h2⟩
    omega
  · rw [if_neg h1, if_neg h2, Finset.erase_eq_of_notMem h1, Finset.erase_eq_of_notMem h2]
    omega

set_option maxHeartbeats 800000 in
open Classical in
/-- **Lemma 23(1), second part.** In the split of a cyclically 4-edge-connected multigraph,
every proper nonempty vertex set has a cut of size at least two. -/
theorem epSp_cut_ge_two {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (p q : W)
    (a b c d m : E) (h : EpCubicD α β L) (h4 : EpCyc4 α β L) (hp : EpPath4 α β L p q a b c d m)
    (hab : epOut α β {p, q} a ≠ epOut α β {p, q} b)
    (hcd : epOut α β {p, q} c ≠ epOut α β {p, q} d)
    (S' : Finset W) (hS' : S' ⊆ L \ {p, q}) (hne : S'.Nonempty) (hneq : S' ≠ L \ {p, q}) :
    2 ≤ (epCut (epSpA α β p q a b c d) (epSpB α β p q a b c d) S').card := by
  by_contra hlt
  obtain ⟨he1, he2, hm⟩ := hp.ends
  have hnl : ∀ g, α g ∈ L → α g ≠ β g := by
    intro g hg
    rcases h.1 g with h' | h'
    · exact h'.2.2
    · exact absurd hg h'.1
  have hlv : ∀ g, β g ∈ L → α g ∈ L := by
    intro g hg
    rcases h.1 g with h' | h'
    · exact h'.1
    · exact absurd (h'.2 ▸ hg) h'.1
  have htouch := hp.touch hnl hlv
  obtain ⟨hpL, hqL, hpq, hsp, hsq, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ := hp
  have hmem : ∀ w, w ∈ ({p, q} : Finset W) ↔ w = p ∨ w = q := by
    intro w; simp only [Finset.mem_insert, Finset.mem_singleton]
  have hpS' : p ∉ S' := fun h' => (Finset.mem_sdiff.mp (hS' h')).2 ((hmem p).mpr (Or.inl rfl))
  have hqS' : q ∉ S' := fun h' => (Finset.mem_sdiff.mp (hS' h')).2 ((hmem q).mpr (Or.inr rfl))
  obtain ⟨oa, hoa⟩ : ∃ oa, oa = epOut α β {p, q} a := ⟨_, rfl⟩
  obtain ⟨ob, hob⟩ : ∃ ob, ob = epOut α β {p, q} b := ⟨_, rfl⟩
  obtain ⟨oc, hoc⟩ : ∃ oc, oc = epOut α β {p, q} c := ⟨_, rfl⟩
  obtain ⟨od, hod⟩ : ∃ od, od = epOut α β {p, q} d := ⟨_, rfl⟩
  rw [← hoa, ← hob] at hab
  rw [← hoc, ← hod] at hcd
  have ha := he1 a (Or.inl rfl)
  have hc := he1 c (Or.inr rfl)
  have hb := he2 b (Or.inl rfl)
  have hd := he2 d (Or.inr rfl)
  rw [← hoa] at ha
  rw [← hoc] at hc
  rw [← hob] at hb
  rw [← hod] at hd
  have hoap : oa ≠ p ∧ oa ≠ q := ⟨fun h' => ha.1 ((hmem _).mpr (Or.inl h')),
    fun h' => ha.1 ((hmem _).mpr (Or.inr h'))⟩
  have hobp : ob ≠ p ∧ ob ≠ q := ⟨fun h' => hb.1 ((hmem _).mpr (Or.inl h')),
    fun h' => hb.1 ((hmem _).mpr (Or.inr h'))⟩
  have hocp : oc ≠ p ∧ oc ≠ q := ⟨fun h' => hc.1 ((hmem _).mpr (Or.inl h')),
    fun h' => hc.1 ((hmem _).mpr (Or.inr h'))⟩
  have hodp : od ≠ p ∧ od ≠ q := ⟨fun h' => hd.1 ((hmem _).mpr (Or.inl h')),
    fun h' => hd.1 ((hmem _).mpr (Or.inr h'))⟩
  obtain ⟨c1, c2, c3, c4⟩ := epSp_cross α β p q a b c d d1 S' hpS'
  rw [← hoa, ← hob] at c1
  rw [← hoc, ← hod] at c2
  -- the lifted set
  obtain ⟨S, hS⟩ : ∃ S : Finset W, S = S' ∪ (if oa ∈ S' then {p} else ∅) ∪
      (if ob ∈ S' then {q} else ∅) := ⟨_, rfl⟩
  have hpS : p ∈ S ↔ oa ∈ S' := by
    rw [hS, Finset.mem_union, Finset.mem_union]
    by_cases hA : oa ∈ S' <;> by_cases hB : ob ∈ S' <;> simp [hA, hB, hpS', hpq]
  have hqS : q ∈ S ↔ ob ∈ S' := by
    rw [hS, Finset.mem_union, Finset.mem_union]
    by_cases hA : oa ∈ S' <;> by_cases hB : ob ∈ S' <;> simp [hA, hB, hqS', hpq.symm]
  have hwS : ∀ w, w ≠ p → w ≠ q → (w ∈ S ↔ w ∈ S') := by
    intro w hwp hwq
    rw [hS, Finset.mem_union, Finset.mem_union]
    by_cases hA : oa ∈ S' <;> by_cases hB : ob ∈ S' <;> simp [hA, hB, hwp, hwq]
  have hS'S : S' ⊆ S := by rw [hS]; exact Finset.subset_union_left.trans Finset.subset_union_left
  have hSL : S ⊆ L := by
    intro w hw
    by_cases hwp : w = p
    · rw [hwp]; exact hpL
    · by_cases hwq : w = q
      · rw [hwq]; exact hqL
      · exact (Finset.mem_sdiff.mp (hS' ((hwS w hwp hwq).mp hw))).1
  obtain ⟨z, hzL', hzS'⟩ : ∃ z, z ∈ L \ {p, q} ∧ z ∉ S' := by
    by_contra hcon
    push_neg at hcon
    exact hneq (Finset.Subset.antisymm hS' hcon)
  have hzp : z ≠ p ∧ z ≠ q := ⟨fun h' => (Finset.mem_sdiff.mp hzL').2 ((hmem _).mpr (Or.inl h')),
    fun h' => (Finset.mem_sdiff.mp hzL').2 ((hmem _).mpr (Or.inr h'))⟩
  have hzS : z ∉ S := fun h' => hzS' ((hwS z hzp.1 hzp.2).mp h')
  have hSne : S.Nonempty := hne.mono hS'S
  have hSneL : S ≠ L := fun h' => hzS (h' ▸ (Finset.mem_sdiff.mp hzL').1)
  have h3 := h4.1 S hSL hSne hSneL
  -- crossing of `S` by the special edges
  have Xa : ¬epCross α β S a := by
    rw [ep_cross_pq α β a p oa ha.2 S, hpS, hwS oa hoap.1 hoap.2]
    exact fun h' => h'.elim (fun h'' => h''.2 h''.1) (fun h'' => h''.1 h''.2)
  have Xb : ¬epCross α β S b := by
    rw [ep_cross_pq α β b q ob hb.2 S, hqS, hwS ob hobp.1 hobp.2]
    exact fun h' => h'.elim (fun h'' => h''.2 h''.1) (fun h'' => h''.1 h''.2)
  have Xm : epCross α β S m ↔ ((oa ∈ S' ∧ ob ∉ S') ∨ (oa ∉ S' ∧ ob ∈ S')) := by
    rw [ep_cross_pq α β m p q hm S, hpS, hqS]
  have Xc : epCross α β S c ↔ ((oa ∈ S' ∧ oc ∉ S') ∨ (oa ∉ S' ∧ oc ∈ S')) := by
    rw [ep_cross_pq α β c p oc hc.2 S, hpS, hwS oc hocp.1 hocp.2]
  have Xd : epCross α β S d ↔ ((ob ∈ S' ∧ od ∉ S') ∨ (ob ∉ S' ∧ od ∈ S')) := by
    rw [ep_cross_pq α β d q od hd.2 S, hqS, hwS od hodp.1 hodp.2]
  have Xrest : ∀ g, ¬(α g ∈ ({p, q} : Finset W) ∨ β g ∈ ({p, q} : Finset W)) →
      (epCross α β S g ↔ epCross α β S' g) := by
    intro g ht
    push_neg at ht
    rw [hmem, hmem] at ht
    push_neg at ht
    unfold epCross
    rw [hwS _ ht.1.1 ht.1.2, hwS _ ht.2.1 ht.2.2]
  -- first merge: rename `m` to `a`
  obtain ⟨S₁, hS₁⟩ : ∃ S₁ : Finset E, ∀ g, g ∈ S₁ ↔
      (if g = a then (a ∈ epCut α β S ∨ m ∈ epCut α β S) else
        if g = m then False else g ∈ epCut α β S) :=
    ⟨Finset.univ.filter (fun g => if g = a then (a ∈ epCut α β S ∨ m ∈ epCut α β S) else
        if g = m then False else g ∈ epCut α β S), fun g => by rw [Finset.mem_filter]; simp⟩
  have e1 : S₁.card = (epCut α β S).card := by
    refine ep_card_merge _ _ a m d2 ?_ ?_ ?_ ?_
    · rw [hS₁, if_pos rfl]
    · rw [hS₁, if_neg d2.symm, if_pos rfl]; exact fun h' => h'
    · rw [mem_epCut]; exact fun h' => Xa h'.1
    · intro g hga hgm; rw [hS₁, if_neg hga, if_neg hgm]
  -- the two cuts agree outside `c`, `d`
  have hpt : ∀ g, g ≠ c → g ≠ d →
      (g ∈ epCut (epSpA α β p q a b c d) (epSpB α β p q a b c d) S' ↔ g ∈ S₁) := by
    intro g hgc hgd
    rw [mem_epCut, hS₁]
    by_cases hga : g = a
    · rw [if_pos hga, hga, mem_epCut, mem_epCut, Xm]
      exact ⟨fun h' => Or.inr (c1.mp h'), fun h' => c1.mpr (h'.resolve_left Xa)⟩
    · rw [if_neg hga]
      by_cases hgm : g = m
      · rw [if_pos hgm, hgm]
        exact ⟨fun h' => (c3 m d2.symm d3.symm ((htouch m).mpr
          (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) h').elim, fun h' => h'.elim⟩
      · rw [if_neg hgm, mem_epCut]
        by_cases ht : α g ∈ ({p, q} : Finset W) ∨ β g ∈ ({p, q} : Finset W)
        · have hgb : g = b := by
            rcases (htouch g).mp ht with e | e | e | e | e
            · exact absurd e hga
            · exact e
            · exact absurd e hgc
            · exact absurd e hgd
            · exact absurd e hgm
          rw [hgb]
          exact ⟨fun h' => (c3 b d7.symm d9.symm ((htouch b).mpr (Or.inr (Or.inl rfl))) h').elim,
            fun h' => (Xb h').elim⟩
        · exact (c4 g hga hgc ht).trans (Xrest g ht).symm
  have hagree : ((epCut (epSpA α β p q a b c d) (epSpB α β p q a b c d) S').erase c).erase d =
      (S₁.erase c).erase d := by
    ext g
    simp only [Finset.mem_erase]
    exact ⟨fun h' => ⟨h'.1, h'.2.1, (hpt g h'.2.1 h'.1).mp h'.2.2⟩,
      fun h' => ⟨h'.1, h'.2.1, (hpt g h'.2.1 h'.1).mpr h'.2.2⟩⟩
  have k1 := ep_card_two (epCut (epSpA α β p q a b c d) (epSpB α β p q a b c d) S') c d d10
  have k2 := ep_card_two S₁ c d d10
  rw [hagree] at k1
  have hdS' : d ∉ epCut (epSpA α β p q a b c d) (epSpB α β p q a b c d) S' := by
    rw [mem_epCut]
    exact c3 d d8.symm d10.symm ((htouch d).mpr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  rw [if_neg hdS'] at k1
  have hcS₁ : c ∈ S₁ ↔ ((oa ∈ S' ∧ oc ∉ S') ∨ (oa ∉ S' ∧ oc ∈ S')) := by
    rw [hS₁, if_neg d1.symm, if_neg d3, mem_epCut, Xc]
  have hdS₁ : d ∈ S₁ ↔ ((ob ∈ S' ∧ od ∉ S') ∨ (ob ∉ S' ∧ od ∈ S')) := by
    rw [hS₁, if_neg d8.symm, if_neg d6, mem_epCut, Xd]
  have hcS' : c ∈ epCut (epSpA α β p q a b c d) (epSpB α β p q a b c d) S' ↔
      ((oc ∈ S' ∧ od ∉ S') ∨ (oc ∉ S' ∧ od ∈ S')) := by rw [mem_epCut]; exact c2
  -- the cut of `S` in `G` has size three, with `oa`, `ob` on one side and `oc`, `od` on the other
  have hlt' : (epCut (epSpA α β p q a b c d) (epSpB α β p q a b c d) S').card ≤ 1 := by omega
  have hthree : c ∈ S₁ ∧ d ∈ S₁ ∧
      c ∉ epCut (epSpA α β p q a b c d) (epSpB α β p q a b c d) S' ∧ (epCut α β S).card = 3 := by
    by_cases x1 : c ∈ S₁ <;> by_cases x2 : d ∈ S₁ <;>
      by_cases x3 : c ∈ epCut (epSpA α β p q a b c d) (epSpB α β p q a b c d) S'
    all_goals
      first
        | rw [if_pos x1] at k2
        | rw [if_neg x1] at k2
      first
        | rw [if_pos x2] at k2
        | rw [if_neg x2] at k2
      first
        | rw [if_pos x3] at k1
        | rw [if_neg x3] at k1
      first
        | exact ⟨x1, x2, x3, by omega⟩
        | omega
  obtain ⟨x1, x2, x3, hS3⟩ := hthree
  have hconf : (oa ∈ S' ∧ ob ∈ S' ∧ oc ∉ S' ∧ od ∉ S') ∨ (oa ∉ S' ∧ ob ∉ S' ∧ oc ∈ S' ∧ od ∈ S') := by
    rcases hcS₁.mp x1 with ⟨hA, hC⟩ | ⟨hA, hC⟩ <;> rcases hdS₁.mp x2 with ⟨hB, hD⟩ | ⟨hB, hD⟩
    · exact Or.inl ⟨hA, hB, hC, hD⟩
    · exact absurd (hcS'.mpr (Or.inr ⟨hC, hD⟩)) x3
    · exact absurd (hcS'.mpr (Or.inl ⟨hC, hD⟩)) x3
    · exact Or.inr ⟨hA, hB, hC, hD⟩
  rcases h4.2 S hSL hS3 with hone | hone
  · rcases hconf with ⟨hA, hB, -, -⟩ | ⟨-, -, hC, hD⟩
    · have : ({p, oa} : Finset W) ⊆ S := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact hpS.mpr hA
        · rw [Finset.mem_singleton.mp hw]; exact hS'S hA
      have := Finset.card_le_card this
      rw [Finset.card_pair hoap.1.symm] at this
      omega
    · have : ({oc, od} : Finset W) ⊆ S := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact hS'S hC
        · rw [Finset.mem_singleton.mp hw]; exact hS'S hD
      have := Finset.card_le_card this
      rw [Finset.card_pair hcd] at this
      omega
  · have hocL : oc ∈ L ∧ od ∈ L := by
      constructor
      · rcases hc.2 with ⟨e1', e2'⟩ | ⟨e1', e2'⟩
        · exact e2' ▸ (by
            rcases h.1 c with h' | h'
            · exact h'.2.1
            · exact absurd (e1' ▸ hpL) h'.1)
        · exact e1' ▸ hlv c (e2' ▸ hpL)
      · rcases hd.2 with ⟨e1', e2'⟩ | ⟨e1', e2'⟩
        · exact e2' ▸ (by
            rcases h.1 d with h' | h'
            · exact h'.2.1
            · exact absurd (e1' ▸ hqL) h'.1)
        · exact e1' ▸ hlv d (e2' ▸ hqL)
    rcases hconf with ⟨-, -, hC, hD⟩ | ⟨hA, hB, -, -⟩
    · have : ({oc, od} : Finset W) ⊆ L \ S := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact Finset.mem_sdiff.mpr ⟨hocL.1, fun h' => hC ((hwS _ hocp.1 hocp.2).mp h')⟩
        · rw [Finset.mem_singleton.mp hw]
          exact Finset.mem_sdiff.mpr ⟨hocL.2, fun h' => hD ((hwS _ hodp.1 hodp.2).mp h')⟩
      have := Finset.card_le_card this
      rw [Finset.card_pair hcd] at this
      omega
    · have : ({p, q} : Finset W) ⊆ L \ S := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact Finset.mem_sdiff.mpr ⟨hpL, fun h' => hA (hpS.mp h')⟩
        · rw [Finset.mem_singleton.mp hw]
          exact Finset.mem_sdiff.mpr ⟨hqL, fun h' => hB (hqS.mp h')⟩
      have := Finset.card_le_card this
      rw [Finset.card_pair hpq] at this
      omega

set_option maxHeartbeats 800000 in
open Classical in
/-- **Lemma 23(4), counting form.** Let `e` be an edge at the outer end of `a` not touching
`p`, `q`. The perfect matchings of the split multigraph containing `e` inject into the perfect
matchings of `G` that contain `e` and avoid `b`. -/
theorem epSp_count {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (p q : W)
    (a b c d m : E) (h : EpCubicD α β L) (hp : EpPath4 α β L p q a b c d m)
    (hab : epOut α β {p, q} a ≠ epOut α β {p, q} b)
    (hcd : epOut α β {p, q} c ≠ epOut α β {p, q} d) (e : E)
    (het : ¬(α e ∈ ({p, q} : Finset W) ∨ β e ∈ ({p, q} : Finset W)))
    (hecr : epCross α β {epOut α β {p, q} a} e) :
    epMe (epSpA α β p q a b c d) (epSpB α β p q a b c d) (L \ {p, q}) e ≤
      ((epPMs α β L).filter (fun M => e ∈ M ∧ b ∉ M)).card := by
  obtain ⟨he1, he2, hm⟩ := hp.ends
  have hnl : ∀ g, α g ∈ L → α g ≠ β g := by
    intro g hg
    rcases h.1 g with h' | h'
    · exact h'.2.2
    · exact absurd hg h'.1
  have hlv : ∀ g, β g ∈ L → α g ∈ L := by
    intro g hg
    rcases h.1 g with h' | h'
    · exact h'.1
    · exact absurd (h'.2 ▸ hg) h'.1
  have htouch := hp.touch hnl hlv
  obtain ⟨hpL, hqL, hpq, hsp, hsq, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ := hp
  have hmem : ∀ w, w ∈ ({p, q} : Finset W) ↔ w = p ∨ w = q := by
    intro w; simp only [Finset.mem_insert, Finset.mem_singleton]
  obtain ⟨oa, hoa⟩ : ∃ oa, oa = epOut α β {p, q} a := ⟨_, rfl⟩
  obtain ⟨ob, hob⟩ : ∃ ob, ob = epOut α β {p, q} b := ⟨_, rfl⟩
  obtain ⟨oc, hoc⟩ : ∃ oc, oc = epOut α β {p, q} c := ⟨_, rfl⟩
  obtain ⟨od, hod⟩ : ∃ od, od = epOut α β {p, q} d := ⟨_, rfl⟩
  rw [← hoa, ← hob] at hab
  rw [← hoc, ← hod] at hcd
  rw [← hoa] at hecr
  have ha := he1 a (Or.inl rfl)
  have hc := he1 c (Or.inr rfl)
  have hb := he2 b (Or.inl rfl)
  have hd := he2 d (Or.inr rfl)
  rw [← hoa] at ha
  rw [← hoc] at hc
  rw [← hob] at hb
  rw [← hod] at hd
  have hnp : ∀ w, w ∉ ({p, q} : Finset W) → w ≠ p ∧ w ≠ q := fun w hw =>
    ⟨fun h' => hw ((hmem _).mpr (Or.inl h')), fun h' => hw ((hmem _).mpr (Or.inr h'))⟩
  -- crossing of singletons in the split multigraph
  have hX : ∀ v, v ≠ p → v ≠ q →
      (epCross (epSpA α β p q a b c d) (epSpB α β p q a b c d) {v} a ↔ (v = oa ∨ v = ob)) ∧
      (epCross (epSpA α β p q a b c d) (epSpB α β p q a b c d) {v} c ↔ (v = oc ∨ v = od)) ∧
      (∀ g, g ≠ a → g ≠ c → (α g ∈ ({p, q} : Finset W) ∨ β g ∈ ({p, q} : Finset W)) →
        ¬epCross (epSpA α β p q a b c d) (epSpB α β p q a b c d) {v} g) ∧
      (∀ g, g ≠ a → g ≠ c → ¬(α g ∈ ({p, q} : Finset W) ∨ β g ∈ ({p, q} : Finset W)) →
        (epCross (epSpA α β p q a b c d) (epSpB α β p q a b c d) {v} g ↔
          epCross α β {v} g)) := by
    intro v hvp hvq
    obtain ⟨c1, c2, c3, c4⟩ := epSp_cross α β p q a b c d d1 {v}
      (fun h' => hvp (Finset.mem_singleton.mp h').symm)
    rw [← hoa, ← hob] at c1
    rw [← hoc, ← hod] at c2
    simp only [Finset.mem_singleton] at c1 c2
    refine ⟨?_, ?_, c3, c4⟩
    · rw [c1]
      constructor
      · rintro (⟨h', -⟩ | ⟨-, h'⟩)
        · exact Or.inl h'.symm
        · exact Or.inr h'.symm
      · rintro (h' | h')
        · exact Or.inl ⟨h'.symm, fun h'' => hab (h'.symm.trans h''.symm)⟩
        · exact Or.inr ⟨fun h'' => hab (h''.trans h'), h'.symm⟩
    · rw [c2]
      constructor
      · rintro (⟨h', -⟩ | ⟨-, h'⟩)
        · exact Or.inl h'.symm
        · exact Or.inr h'.symm
      · rintro (h' | h')
        · exact Or.inl ⟨h'.symm, fun h'' => hcd (h'.symm.trans h''.symm)⟩
        · exact Or.inr ⟨fun h'' => hcd (h''.trans h'), h'.symm⟩
  -- crossing in `G` by `c`, `d`, `m`
  have hGc : ∀ v, v ≠ p → (epCross α β {v} c ↔ v = oc) := by
    intro v hvp
    rw [epCross_singleton]
    rcases hc.2 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
    · exact ⟨fun h' => h'.elim (fun h'' => absurd h''.1.symm hvp) (fun h'' => h''.2.symm),
        fun h' => Or.inr ⟨fun h'' => hvp h''.symm, h'.symm⟩⟩
    · exact ⟨fun h' => h'.elim (fun h'' => h''.1.symm) (fun h'' => absurd h''.2.symm hvp),
        fun h' => Or.inl ⟨h'.symm, fun h'' => hvp h''.symm⟩⟩
  have hGd : ∀ v, v ≠ q → (epCross α β {v} d ↔ v = od) := by
    intro v hvq
    rw [epCross_singleton]
    rcases hd.2 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
    · exact ⟨fun h' => h'.elim (fun h'' => absurd h''.1.symm hvq) (fun h'' => h''.2.symm),
        fun h' => Or.inr ⟨fun h'' => hvq h''.symm, h'.symm⟩⟩
    · exact ⟨fun h' => h'.elim (fun h'' => h''.1.symm) (fun h'' => absurd h''.2.symm hvq),
        fun h' => Or.inl ⟨h'.symm, fun h'' => hvq h''.symm⟩⟩
  have hGm : ∀ v, v ≠ p → v ≠ q → ¬epCross α β {v} m := by
    intro v hvp hvq
    rw [epCross_singleton]
    rcases hm with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
    · exact fun h' => h'.elim (fun h'' => hvp h''.1.symm) (fun h'' => hvq h''.2.symm)
    · exact fun h' => h'.elim (fun h'' => hvq h''.1.symm) (fun h'' => hvp h''.2.symm)
  have hoap := hnp oa ha.1
  have hocp := hnp oc hc.1
  have hodp := hnp od hd.1
  have hoaL : oa ∈ L := by
    rw [epCross_singleton] at hecr
    rcases h.1 e with ⟨l1, l2, -⟩ | ⟨l1, l2⟩
    · rcases hecr with ⟨e1, -⟩ | ⟨-, e2⟩
      · exact e1 ▸ l1
      · exact e2 ▸ l2
    · rcases hecr with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact absurd (l2.trans e1) e2
      · exact absurd (l2.symm.trans e2) e1
  have hea : e ≠ a := fun h' => het ((htouch e).mpr (Or.inl h'))
  have hec : e ≠ c := fun h' => het ((htouch e).mpr (Or.inr (Or.inr (Or.inl h'))))
  have hoaL' : oa ∈ L \ ({p, q} : Finset W) := Finset.mem_sdiff.mpr ⟨hoaL, ha.1⟩
  have hsame : ∀ g, g ≠ a → g ≠ c → ¬(α g ∈ ({p, q} : Finset W) ∨ β g ∈ ({p, q} : Finset W)) →
      epSpA α β p q a b c d g = α g ∧ epSpB α β p q a b c d g = β g := by
    intro g hga hgc ht
    unfold epSpA epSpB
    rw [if_neg hga, if_neg hga, if_neg hgc, if_neg hgc, if_neg ht, if_neg ht]
    exact ⟨rfl, rfl⟩
  have hdead : ∀ g, g ≠ a → g ≠ c → (α g ∈ ({p, q} : Finset W) ∨ β g ∈ ({p, q} : Finset W)) →
      epSpA α β p q a b c d g = epSpB α β p q a b c d g := by
    intro g hga hgc ht
    unfold epSpA epSpB
    rw [if_neg hga, if_neg hga, if_neg hgc, if_neg hgc, if_pos ht, if_pos ht]
  -- facts about a perfect matching of the split multigraph containing `e`
  have hfacts : ∀ M' : Finset E,
      M' ∈ epPM (epSpA α β p q a b c d) (epSpB α β p q a b c d) (L \ {p, q}) → e ∈ M' →
      a ∉ M' ∧ ∀ g ∈ M', g ≠ c →
        ¬(α g ∈ ({p, q} : Finset W) ∨ β g ∈ ({p, q} : Finset W)) := by
    intro M' hM' heM'
    have haM : a ∉ M' := by
      intro haM
      obtain ⟨g₀, -, huniq⟩ := hM'.2 oa hoaL'
      have x1 := huniq a ⟨haM, ((hX oa hoap.1 hoap.2).1).mpr (Or.inl rfl)⟩
      have x2 := huniq e ⟨heM', ((hX oa hoap.1 hoap.2).2.2.2 e hea hec het).mpr hecr⟩
      exact hea (x2.trans x1.symm)
    refine ⟨haM, fun g hg hgc ht => ?_⟩
    exact hM'.1 g hg (hdead g (fun h' => haM (h' ▸ hg)) hgc ht)
  have hnotin : ∀ M' : Finset E,
      M' ∈ epPM (epSpA α β p q a b c d) (epSpB α β p q a b c d) (L \ {p, q}) → e ∈ M' →
      b ∉ M' ∧ d ∉ M' ∧ m ∉ M' := by
    intro M' hM' heM'
    obtain ⟨-, f2⟩ := hfacts M' hM' heM'
    exact ⟨fun h' => f2 b h' d9.symm ((htouch b).mpr (Or.inr (Or.inl rfl))),
      fun h' => f2 d h' d10.symm ((htouch d).mpr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))),
      fun h' => f2 m h' d3.symm ((htouch m).mpr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))⟩
  unfold epMe
  refine Finset.card_le_card_of_injOn (fun M' => M' ∪ (if c ∈ M' then {d} else {m}))
    (fun M' hM'f => ?_) (fun M₁ hM₁ M₂ hM₂ heq => ?_)
  · -- the extension is a perfect matching of `G` containing `e` and avoiding `b`
    obtain ⟨hM'p, heM'⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hM'f)
    have hM' := (mem_epPMs _ _ _ M').mp hM'p
    obtain ⟨f1, f2⟩ := hfacts M' hM' heM'
    obtain ⟨nb, nd, nm⟩ := hnotin M' hM' heM'
    have hXmem : ∀ g, g ∈ M' ∪ (if c ∈ M' then ({d} : Finset E) else {m}) ↔
        g ∈ M' ∨ (c ∈ M' ∧ g = d) ∨ (c ∉ M' ∧ g = m) := by
      intro g
      by_cases hcM : c ∈ M'
      · rw [if_pos hcM, Finset.mem_union, Finset.mem_singleton]
        exact ⟨fun h' => h'.elim Or.inl (fun h'' => Or.inr (Or.inl ⟨hcM, h''⟩)),
          fun h' => h'.elim Or.inl (fun h'' => h''.elim (fun h3 => Or.inr h3.2)
            (fun h3 => absurd hcM h3.1))⟩
      · rw [if_neg hcM, Finset.mem_union, Finset.mem_singleton]
        exact ⟨fun h' => h'.elim Or.inl (fun h'' => Or.inr (Or.inr ⟨hcM, h''⟩)),
          fun h' => h'.elim Or.inl (fun h'' => h''.elim (fun h3 => absurd h3.1 hcM)
            (fun h3 => Or.inr h3.2))⟩
    have hT : ∀ g ∈ M', g ≠ c → ∀ v, v ≠ p → v ≠ q →
        (epCross (epSpA α β p q a b c d) (epSpB α β p q a b c d) {v} g ↔ epCross α β {v} g) :=
      fun g hg hgc v hvp hvq =>
        (hX v hvp hvq).2.2.2 g (fun h' => f1 (h' ▸ hg)) hgc (f2 g hg hgc)
    have hbM : b ∉ M' ∪ (if c ∈ M' then ({d} : Finset E) else {m}) := by
      intro hh
      rcases (hXmem b).mp hh with h' | ⟨-, h'⟩ | ⟨-, h'⟩
      · exact nb h'
      · exact d4 h'
      · exact d5 h'
    have haM : a ∉ M' ∪ (if c ∈ M' then ({d} : Finset E) else {m}) := by
      intro hh
      rcases (hXmem a).mp hh with h' | ⟨-, h'⟩ | ⟨-, h'⟩
      · exact f1 h'
      · exact d8 h'
      · exact d2 h'
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨(mem_epPMs _ _ _ _).mpr ⟨?_, ?_⟩,
      (hXmem e).mpr (Or.inl heM'), hbM⟩)
    · intro g hg
      rcases (hXmem g).mp hg with h' | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · by_cases hgc : g = c
        · rw [hgc]
          rcases hc.2 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
          · exact hocp.1.symm
          · exact hocp.1
        · have hs := hsame g (fun h'' => f1 (h'' ▸ h')) hgc (f2 g h' hgc)
          rw [← hs.1, ← hs.2]
          exact hM'.1 g h'
      · rcases hd.2 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
        · exact hodp.2.symm
        · exact hodp.2
      · rcases hm with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
        · exact hpq
        · exact hpq.symm
    · intro v hv
      by_cases hvp : v = p
      · rw [hvp]
        by_cases hcM : c ∈ M'
        · refine ⟨c, ⟨(hXmem c).mpr (Or.inl hcM), (hsp c).mpr (Or.inr (Or.inl rfl))⟩,
            fun g hg => ?_⟩
          rcases (hsp g).mp hg.2 with rfl | rfl | rfl
          · exact absurd hg.1 haM
          · rfl
          · rcases (hXmem _).mp hg.1 with h' | ⟨-, h'⟩ | ⟨h', -⟩
            · exact absurd h' nm
            · exact absurd h' d6.symm
            · exact absurd hcM h'
        · refine ⟨m, ⟨(hXmem m).mpr (Or.inr (Or.inr ⟨hcM, rfl⟩)),
            (hsp m).mpr (Or.inr (Or.inr rfl))⟩, fun g hg => ?_⟩
          rcases (hsp g).mp hg.2 with rfl | rfl | rfl
          · exact absurd hg.1 haM
          · rcases (hXmem _).mp hg.1 with h' | ⟨h', -⟩ | ⟨-, h'⟩
            · exact absurd h' hcM
            · exact absurd h' hcM
            · exact h'
          · rfl
      · by_cases hvq : v = q
        · rw [hvq]
          by_cases hcM : c ∈ M'
          · refine ⟨d, ⟨(hXmem d).mpr (Or.inr (Or.inl ⟨hcM, rfl⟩)),
              (hsq d).mpr (Or.inr (Or.inl rfl))⟩, fun g hg => ?_⟩
            rcases (hsq g).mp hg.2 with rfl | rfl | rfl
            · exact absurd hg.1 hbM
            · rfl
            · rcases (hXmem _).mp hg.1 with h' | ⟨-, h'⟩ | ⟨h', -⟩
              · exact absurd h' nm
              · exact h'
              · exact absurd hcM h'
          · refine ⟨m, ⟨(hXmem m).mpr (Or.inr (Or.inr ⟨hcM, rfl⟩)),
              (hsq m).mpr (Or.inr (Or.inr rfl))⟩, fun g hg => ?_⟩
            rcases (hsq g).mp hg.2 with rfl | rfl | rfl
            · exact absurd hg.1 hbM
            · rcases (hXmem _).mp hg.1 with h' | ⟨h', -⟩ | ⟨-, h'⟩
              · exact absurd h' nd
              · exact absurd h' hcM
              · exact h'
            · rfl
        · have hvL' : v ∈ L \ ({p, q} : Finset W) := Finset.mem_sdiff.mpr
            ⟨hv, fun h' => ((hmem v).mp h').elim hvp hvq⟩
          obtain ⟨g₀, ⟨hg₀M, hg₀c⟩, huniq⟩ := hM'.2 v hvL'
          have hXc := (hX v hvp hvq).2.1
          by_cases hcase : c ∈ M' ∧ v = od
          · have hg₀ : g₀ = c := (huniq c ⟨hcase.1, hXc.mpr (Or.inr hcase.2)⟩).symm
            refine ⟨d, ⟨(hXmem d).mpr (Or.inr (Or.inl ⟨hcase.1, rfl⟩)),
              (hGd v hvq).mpr hcase.2⟩, fun g hg => ?_⟩
            rcases (hXmem g).mp hg.1 with h' | ⟨-, h'⟩ | ⟨h', -⟩
            · by_cases hgc : g = c
              · rw [hgc, hGc v hvp] at hg
                exact absurd (hg.2.symm.trans hcase.2) hcd
              · exact absurd ((huniq g ⟨h', (hT g h' hgc v hvp hvq).mpr hg.2⟩).trans hg₀) hgc
            · exact h'
            · exact absurd hcase.1 h'
          · have hg₀G : epCross α β {v} g₀ := by
              by_cases hgc : g₀ = c
              · rw [hgc] at hg₀c hg₀M ⊢
                rcases hXc.mp hg₀c with h' | h'
                · exact (hGc v hvp).mpr h'
                · exact absurd ⟨hg₀M, h'⟩ hcase
              · exact (hT g₀ hg₀M hgc v hvp hvq).mp hg₀c
            refine ⟨g₀, ⟨(hXmem g₀).mpr (Or.inl hg₀M), hg₀G⟩, fun g hg => ?_⟩
            rcases (hXmem g).mp hg.1 with h' | ⟨h', rfl⟩ | ⟨-, rfl⟩
            · by_cases hgc : g = c
              · rw [hgc] at hg h' ⊢
                exact huniq c ⟨h', hXc.mpr (Or.inl ((hGc v hvp).mp hg.2))⟩
              · exact huniq g ⟨h', (hT g h' hgc v hvp hvq).mpr hg.2⟩
            · exact absurd ⟨h', (hGd v hvq).mp hg.2⟩ hcase
            · exact absurd hg.2 (hGm v hvp hvq)
  · -- injectivity
    obtain ⟨hM₁p, heM₁⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hM₁)
    obtain ⟨hM₂p, heM₂⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hM₂)
    obtain ⟨-, nd₁, nm₁⟩ := hnotin M₁ ((mem_epPMs _ _ _ M₁).mp hM₁p) heM₁
    obtain ⟨-, nd₂, nm₂⟩ := hnotin M₂ ((mem_epPMs _ _ _ M₂).mp hM₂p) heM₂
    have key : ∀ (A B : Finset E), d ∉ A → m ∉ A →
        A ∪ (if c ∈ A then ({d} : Finset E) else {m}) =
          B ∪ (if c ∈ B then ({d} : Finset E) else {m}) → A ⊆ B := by
      intro A B hdA hmA hAB g hg
      have : g ∈ B ∪ (if c ∈ B then ({d} : Finset E) else {m}) := by
        rw [← hAB]; exact Finset.mem_union_left _ hg
      rcases Finset.mem_union.mp this with h' | h'
      · exact h'
      · by_cases hcB : c ∈ B
        · rw [if_pos hcB, Finset.mem_singleton] at h'
          exact absurd (h' ▸ hg) hdA
        · rw [if_neg hcB, Finset.mem_singleton] at h'
          exact absurd (h' ▸ hg) hmA
    exact Finset.Subset.antisymm (key M₁ M₂ nd₁ nm₁ heq) (key M₂ M₁ nd₂ nm₂ heq.symm)

lemma EpCyc4.bridgelessD {W E : Type*} [Fintype E] {α β : E → W} {L : Finset W}
    (h : EpCubicD α β L) (h4 : EpCyc4 α β L) : EpBridgeless α β L ∧ EpConnected α β L := by
  classical
  refine ⟨fun T hT h1 => ?_, fun T hT hne hneL h0 => ?_⟩
  · by_cases hTe : T.Nonempty
    · by_cases hTL : T = L
      · have : epCut α β T = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro g hg
          rw [mem_epCut, hTL] at hg
          unfold epCross at hg
          rcases h.1 g with ⟨l1, l2, -⟩ | ⟨l1, l2⟩
          · tauto
          · rw [l2] at hg; tauto
        rw [this, Finset.card_empty] at h1
        exact absurd h1 (by norm_num)
      · have := h4.1 T hT hTe hTL
        omega
    · rw [Finset.not_nonempty_iff_eq_empty] at hTe
      have : epCut α β T = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro g hg
        rw [mem_epCut, hTe] at hg
        unfold epCross at hg
        simp at hg
      rw [this, Finset.card_empty] at h1
      exact absurd h1 (by norm_num)
  · have := h4.1 T hT hne hneL
    rw [h0, Finset.card_empty] at this
    omega

open Classical in
/-- A cyclically 4-edge-connected multigraph with at least six vertices has no triangle. -/
lemma ep_cyc4_no_triangle {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (h : EpCubicD α β L) (h4 : EpCyc4 α β L) (h6 : 6 ≤ L.card) (x y z : W) (exy eyz ezx : E) :
    ¬EpTriangle α β L x y z exy eyz ezx := by
  intro ht
  obtain ⟨hb, hconn⟩ := EpCyc4.bridgelessD h h4
  obtain ⟨hTL, hT3, hTcut⟩ := ep_triangle_cut α β L h hb hconn (by omega) x y z exy eyz ezx ht
  have := Finset.card_sdiff_add_card_eq_card hTL
  rcases h4.2 _ hTL hTcut with h' | h' <;> omega

/-- A rootless foliage: pairwise disjoint burls. -/
def EpFol0 {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (𝒳 : Finset (Finset W)) : Prop :=
  (∀ X ∈ 𝒳, X ⊆ L ∧ EpBurl α β X) ∧ ∀ X ∈ 𝒳, ∀ X' ∈ 𝒳, X ≠ X' → Disjoint X X'

set_option maxHeartbeats 800000 in
open Classical in
/-- **Lemma 10 with weights.** A foliage of the contraction of a triangle lifts to a foliage of
the multigraph of at least the same weight. -/
theorem ep_fol_tri_lift {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (x y z : W) (exy eyz ezx : E) (h : EpCubicD α β L)
    (ht : EpTriangle α β L x y z exy eyz ezx)
    (h3 : (epCut α β ({x, y, z} : Finset W)).card = 3) (𝒳₁ : Finset (Finset W))
    (hfol : EpFol0 (epConA α β ({x, y, z} : Finset W) x y) (epConB α β ({x, y, z} : Finset W) x y)
      (epL' L ({x, y, z} : Finset W) x) 𝒳₁) :
    ∃ 𝒳, EpFol0 α β L 𝒳 ∧
      epFw (epConA α β ({x, y, z} : Finset W) x y) (epConB α β ({x, y, z} : Finset W) x y) 𝒳₁ ≤
        epFw α β 𝒳 := by
  have hxT : x ∈ ({x, y, z} : Finset W) := Finset.mem_insert_self _ _
  have hyT : y ∈ ({x, y, z} : Finset W) := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hTL : ({x, y, z} : Finset W) ⊆ L := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact ht.1
    · exact ht.2.1
    · exact ht.2.2.1
  have hyx : y ≠ x := ht.2.2.2.1.symm
  obtain ⟨f, hf⟩ : ∃ f : Finset W → Finset W, ∀ Z, f Z = if x ∈ Z then Z ∪ {x, y, z} else Z :=
    ⟨_, fun _ => rfl⟩
  have hsubL1 : ∀ Z ∈ 𝒳₁, ∀ w, w ∈ Z → w ≠ x → w ∈ L ∧ w ∉ ({x, y, z} : Finset W) := by
    intro Z hZ w hw hwx
    have := (hfol.1 Z hZ).1 hw
    unfold epL' at this
    rcases Finset.mem_insert.mp this with h' | h'
    · exact absurd h' hwx
    · exact Finset.mem_sdiff.mp h'
  -- properties of the lift of one member
  have hone : ∀ Z ∈ 𝒳₁, f Z ⊆ L ∧ EpBurl α β (f Z) ∧
      ((if EpTwig (epConA α β ({x, y, z} : Finset W) x y)
        (epConB α β ({x, y, z} : Finset W) x y) Z then (196 : ℝ) / 995 else 98 / 995) ≤
        (if EpTwig α β (f Z) then (196 : ℝ) / 995 else 98 / 995)) := by
    intro Z hZ
    obtain ⟨hZL1, hZb⟩ := hfol.1 Z hZ
    rw [hf]
    by_cases hxZ : x ∈ Z
    · rw [if_pos hxZ]
      have hcut := epCon_cut α β L ({x, y, z} : Finset W) x y hxT Z hZL1
      unfold epLift at hcut
      rw [if_pos hxZ] at hcut
      refine ⟨Finset.union_subset (fun w hw => ?_) hTL,
        ep_triangle_burl_lift α β L x y z exy eyz ezx h ht h3 Z hZL1 hxZ hZb, ?_⟩
      · by_cases hwx : w = x
        · rw [hwx]; exact ht.1
        · exact (hsubL1 Z hZ w hw hwx).1
      · by_cases htw : EpTwig (epConA α β ({x, y, z} : Finset W) x y)
            (epConB α β ({x, y, z} : Finset W) x y) Z
        · have : EpTwig α β (Z ∪ {x, y, z}) := by
            unfold EpTwig at htw ⊢
            rw [← hcut]
            rcases htw with h' | ⟨h', h''⟩
            · exact Or.inl h'
            · exact Or.inr ⟨h', h''.trans (Finset.card_le_card Finset.subset_union_left)⟩
          rw [if_pos htw, if_pos this]
        · rw [if_neg htw]; split_ifs <;> norm_num
    · rw [if_neg hxZ]
      have hZ' : Z ⊆ L ∧ ∀ w, w ∈ Z → w ∉ ({x, y, z} : Finset W) :=
        ⟨fun w hw => (hsubL1 Z hZ w hw (fun h' => hxZ (h' ▸ hw))).1,
          fun w hw => (hsubL1 Z hZ w hw (fun h' => hxZ (h' ▸ hw))).2⟩
      obtain ⟨b1, b2⟩ := epCon_burl α β L ({x, y, z} : Finset W) Z x y h hTL hxT hyT hZ'.1 hZ'.2 hZb
      refine ⟨hZ'.1, b1, ?_⟩
      have : EpTwig α β Z ↔ EpTwig (epConA α β ({x, y, z} : Finset W) x y)
          (epConB α β ({x, y, z} : Finset W) x y) Z := by
        unfold EpTwig; rw [b2]
      by_cases htw : EpTwig α β Z
      · rw [if_pos htw, if_pos (this.mp htw)]
      · rw [if_neg htw, if_neg (fun h' => htw (this.mpr h'))]
  -- membership in a lift
  have hfmem : ∀ Z ∈ 𝒳₁, ∀ w, w ∈ f Z → w ∈ Z ∨ (x ∈ Z ∧ w ∈ ({x, y, z} : Finset W)) := by
    intro Z hZ w hw
    rw [hf] at hw
    by_cases hxZ : x ∈ Z
    · rw [if_pos hxZ] at hw
      exact (Finset.mem_union.mp hw).elim Or.inl (fun h' => Or.inr ⟨hxZ, h'⟩)
    · rw [if_neg hxZ] at hw; exact Or.inl hw
  have hsubf : ∀ Z, Z ⊆ f Z := by
    intro Z
    rw [hf]
    by_cases hxZ : x ∈ Z
    · rw [if_pos hxZ]; exact Finset.subset_union_left
    · rw [if_neg hxZ]
  have hdisj : ∀ Z ∈ 𝒳₁, ∀ Z' ∈ 𝒳₁, Z ≠ Z' → Disjoint (f Z) (f Z') := by
    intro Z hZ Z' hZ' hne
    have hd := hfol.2 Z hZ Z' hZ' hne
    rw [Finset.disjoint_left] at hd ⊢
    intro w hw hw'
    rcases hfmem Z hZ w hw with a1 | ⟨a1, a2⟩ <;> rcases hfmem Z' hZ' w hw' with b1 | ⟨b1, b2⟩
    · exact hd a1 b1
    · by_cases hwx : w = x
      · exact hd (hwx ▸ a1) b1
      · exact (hsubL1 Z hZ w a1 hwx).2 b2
    · by_cases hwx : w = x
      · exact hd a1 (hwx ▸ b1)
      · exact (hsubL1 Z' hZ' w b1 hwx).2 a2
    · exact hd a1 b1
  have hinj : Set.InjOn f (𝒳₁ : Set (Finset W)) := by
    intro Z hZ Z' hZ' hff
    by_contra hne
    have hd := hdisj Z hZ Z' hZ' hne
    by_cases hZe : Z.Nonempty
    · obtain ⟨w, hw⟩ := hZe
      exact Finset.disjoint_left.mp hd (hsubf Z hw) (hff ▸ hsubf Z hw)
    · rw [Finset.not_nonempty_iff_eq_empty] at hZe
      by_cases hZe' : Z'.Nonempty
      · obtain ⟨w, hw⟩ := hZe'
        exact Finset.disjoint_left.mp hd (hff ▸ hsubf Z' hw) (hsubf Z' hw)
      · rw [Finset.not_nonempty_iff_eq_empty] at hZe'
        exact hne (hZe.trans hZe'.symm)
  refine ⟨𝒳₁.image f, ⟨fun X hX => ?_, fun X hX X' hX' hne => ?_⟩, ?_⟩
  · obtain ⟨Z, hZ, rfl⟩ := Finset.mem_image.mp hX
    exact ⟨(hone Z hZ).1, (hone Z hZ).2.1⟩
  · obtain ⟨Z, hZ, rfl⟩ := Finset.mem_image.mp hX
    obtain ⟨Z', hZ', rfl⟩ := Finset.mem_image.mp hX'
    exact hdisj Z hZ Z' hZ' (fun h' => hne (by rw [h']))
  · unfold epFw
    rw [Finset.sum_image hinj]
    exact Finset.sum_le_sum (fun Z hZ => (hone Z hZ).2.2)

lemma ep_ends_profile {W E : Type*} (α β : E → W) (X : Finset W) (g : E) (s t : W)
    (h : (α g = s ∧ β g = t) ∨ (α g = t ∧ β g = s)) :
    ((α g ∈ X ∨ β g ∈ X) ↔ (s ∈ X ∨ t ∈ X)) ∧ ((α g ∈ X ∧ β g ∈ X) ↔ (s ∈ X ∧ t ∈ X)) ∧
      (s ≠ t → ∀ v, (epCross α β {v} g ↔ v = s ∨ v = t)) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨by rw [h1, h2], by rw [h1, h2], fun hst v => ?_⟩
    exact ep_edge_cross α β s t g hst (Or.inl ⟨h1, h2⟩) v
  · refine ⟨by rw [h1, h2]; exact or_comm, by rw [h1, h2]; exact and_comm, fun hst v => ?_⟩
    exact ep_edge_cross α β s t g hst (Or.inr ⟨h1, h2⟩) v

set_option maxHeartbeats 800000 in
open Classical in
/-- Every triangle of the split of a triangle-free multigraph uses one of the two new edges. -/
theorem epSp_triangle_new {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (p q : W)
    (a b c d m : E) (hac : a ≠ c)
    (hnotri : ∀ x y z e1 e2 e3, ¬EpTriangle α β L x y z e1 e2 e3)
    (x y z : W) (e1 e2 e3 : E)
    (ht : EpTriangle (epSpA α β p q a b c d) (epSpB α β p q a b c d) (L \ {p, q}) x y z e1 e2 e3) :
    (e1 = a ∨ e1 = c) ∨ (e2 = a ∨ e2 = c) ∨ (e3 = a ∨ e3 = c) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨⟨n1, n2⟩, ⟨n3, n4⟩, n5, n6⟩ := hcon
  obtain ⟨hx, hy, hz, hxy, hyz, hxz, c1, c2, c3⟩ := ht
  have hmem : ∀ w, w ∈ ({p, q} : Finset W) ↔ w = p ∨ w = q := by
    intro w; simp only [Finset.mem_insert, Finset.mem_singleton]
  have hne : ∀ w, w ∈ L \ ({p, q} : Finset W) → w ≠ p := fun w hw h' =>
    (Finset.mem_sdiff.mp hw).2 ((hmem w).mpr (Or.inl h'))
  -- a triangle edge different from the new edges has its old ends
  have hedge : ∀ (g : E) (u : W), g ≠ a → g ≠ c → u ∈ L \ ({p, q} : Finset W) →
      epCross (epSpA α β p q a b c d) (epSpB α β p q a b c d) {u} g →
      epSpA α β p q a b c d g = α g ∧ epSpB α β p q a b c d g = β g := by
    intro g u hga hgc hu hcr
    obtain ⟨-, -, k3, -⟩ := epSp_cross α β p q a b c d hac {u}
      (fun h' => hne u hu (Finset.mem_singleton.mp h').symm)
    have ht : ¬(α g ∈ ({p, q} : Finset W) ∨ β g ∈ ({p, q} : Finset W)) :=
      fun ht => k3 g hga hgc ht hcr
    unfold epSpA epSpB
    rw [if_neg hga, if_neg hga, if_neg hgc, if_neg hgc, if_neg ht, if_neg ht]
    exact ⟨rfl, rfl⟩
  have hcr : ∀ (g : E) (u : W), g ≠ a → g ≠ c → u ∈ L \ ({p, q} : Finset W) →
      epCross (epSpA α β p q a b c d) (epSpB α β p q a b c d) {u} g →
      ∀ w, (epCross α β {w} g ↔ epCross (epSpA α β p q a b c d) (epSpB α β p q a b c d) {w} g) := by
    intro g u hga hgc hu hcr w
    obtain ⟨k1, k2⟩ := hedge g u hga hgc hu hcr
    rw [epCross_singleton, epCross_singleton, k1, k2]
  have t1 := hcr e1 x n1 n2 hx ((c1 x).mpr (Or.inl rfl))
  have t2 := hcr e2 y n3 n4 hy ((c2 y).mpr (Or.inl rfl))
  have t3 := hcr e3 z n5 n6 hz ((c3 z).mpr (Or.inl rfl))
  exact hnotri x y z e1 e2 e3 ⟨(Finset.mem_sdiff.mp hx).1, (Finset.mem_sdiff.mp hy).1,
    (Finset.mem_sdiff.mp hz).1, hxy, hyz, hxz, fun w => (t1 w).trans (c1 w),
    fun w => (t2 w).trans (c2 w), fun w => (t3 w).trans (c3 w)⟩

set_option maxHeartbeats 1600000 in
open Classical in
/-- **Pruning with a budget.** If every triangle has an edge in the set `Q`, then at most `|Q|`
contractions of irrelevant triangles give a pruned multigraph; foliages lift without loss. -/
theorem ep_prune_budget {W E : Type*} [Fintype E] : ∀ (k : ℕ) (α β : E → W) (L : Finset W)
    (Q : Finset E), Q.card = k → EpCubicD α β L → EpBridgeless α β L → EpConnected α β L →
    (∀ x y z e1 e2 e3, EpTriangle α β L x y z e1 e2 e3 → e1 ∈ Q ∨ e2 ∈ Q ∨ e3 ∈ Q) →
    2 * k + 5 ≤ L.card →
    ∃ (α' β' : E → W) (L' : Finset W), EpReach α β L α' β' L' ∧ EpPruned α' β' L' ∧
      L.card ≤ L'.card + 2 * k ∧ L'.card ≤ L.card ∧
      ∀ 𝒳', EpFol0 α' β' L' 𝒳' → ∃ 𝒳, EpFol0 α β L 𝒳 ∧ epFw α' β' 𝒳' ≤ epFw α β 𝒳 := by
  intro k
  induction k with
  | zero =>
    intro α β L Q hQ h hb hconn htri hbig
    refine ⟨α, β, L, Relation.ReflTransGen.refl, ?_, by omega, le_refl _,
      fun 𝒳' h' => ⟨𝒳', h', le_refl _⟩⟩
    intro x y z e1 e2 e3 ht
    rw [Finset.card_eq_zero] at hQ
    have := htri x y z e1 e2 e3 ht
    rw [hQ] at this
    simp at this
  | succ k ih =>
    intro α β L Q hQ h hb hconn htri hbig
    by_cases hpr : EpPruned α β L
    · exact ⟨α, β, L, Relation.ReflTransGen.refl, hpr, by omega, le_refl _,
        fun 𝒳' h' => ⟨𝒳', h', le_refl _⟩⟩
    · unfold EpPruned at hpr
      push_neg at hpr
      obtain ⟨x, y, z, e1, e2, e3, ht, hirr⟩ := hpr
      obtain ⟨hTL, hT3, hTcut⟩ := ep_triangle_cut α β L h hb hconn (by omega) x y z e1 e2 e3 ht
      have hxT : x ∈ ({x, y, z} : Finset W) := Finset.mem_insert_self _ _
      have hyT : y ∈ ({x, y, z} : Finset W) :=
        Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      have hzT : z ∈ ({x, y, z} : Finset W) :=
        Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      have hxy : x ≠ y := ht.2.2.2.1
      have hstep : EpStep α β L (epConA α β ({x, y, z} : Finset W) x y)
          (epConB α β ({x, y, z} : Finset W) x y) (epL' L ({x, y, z} : Finset W) x) :=
        Or.inl ⟨_, x, y, hTL, hxT, hyT, hxy.symm, hTcut, rfl, rfl, rfl⟩
      obtain ⟨h₁, hb₁, hconn₁, -, -⟩ := hstep.preserves h hb hconn
      have hcard : (epL' L ({x, y, z} : Finset W) x).card + 2 = L.card := by
        have e1' := Finset.card_sdiff_add_card_eq_card hTL
        have e2' : (epL' L ({x, y, z} : Finset W) x).card = (L \ ({x, y, z} : Finset W)).card + 1 :=
          Finset.card_insert_of_notMem (fun h' => (Finset.mem_sdiff.mp h').2 hxT)
        omega
      -- an edge of the contracted triangle lies in `Q`
      obtain ⟨q₀, hq₀Q, hq₀⟩ : ∃ q₀ ∈ Q, ∃ t ∈ ({x, y, z} : Finset W), epCross α β {t} q₀ := by
        have ⟨_, _, _, _, _, _, c1, c2, c3⟩ := ht
        rcases htri x y z e1 e2 e3 ht with h' | h' | h'
        · exact ⟨e1, h', x, hxT, (c1 x).mpr (Or.inl rfl)⟩
        · exact ⟨e2, h', y, hyT, (c2 y).mpr (Or.inl rfl)⟩
        · exact ⟨e3, h', z, hzT, (c3 z).mpr (Or.inl rfl)⟩
      obtain ⟨t, htT, htq⟩ := hq₀
      have htri₁ : ∀ p' q' s' f1 f2 f3,
          EpTriangle (epConA α β ({x, y, z} : Finset W) x y) (epConB α β ({x, y, z} : Finset W) x y)
            (epL' L ({x, y, z} : Finset W) x) p' q' s' f1 f2 f3 →
          f1 ∈ Q.erase q₀ ∨ f2 ∈ Q.erase q₀ ∨ f3 ∈ Q.erase q₀ := by
        intro p' q' s' f1 f2 f3 ht₁
        obtain ⟨a1, a2, a3, -⟩ := ep_tri_contract_triangle α β L x y z hxy.symm hirr
          p' q' s' f1 f2 f3 ht₁
        obtain ⟨ht₂, hpT, hqT, hsT⟩ := epCon_triangle_back α β L ({x, y, z} : Finset W) x y hxT hyT
          p' q' s' f1 f2 f3 ht₁ a1 a2 a3
        have ⟨_, _, _, _, _, _, c1, c2, c3⟩ := ht₂
        have hne1 : f1 ≠ q₀ := fun h' => by
          rw [← h', c1] at htq
          exact htq.elim (fun h'' => hpT (h'' ▸ htT)) (fun h'' => hqT (h'' ▸ htT))
        have hne2 : f2 ≠ q₀ := fun h' => by
          rw [← h', c2] at htq
          exact htq.elim (fun h'' => hqT (h'' ▸ htT)) (fun h'' => hsT (h'' ▸ htT))
        have hne3 : f3 ≠ q₀ := fun h' => by
          rw [← h', c3] at htq
          exact htq.elim (fun h'' => hsT (h'' ▸ htT)) (fun h'' => hpT (h'' ▸ htT))
        rcases htri p' q' s' f1 f2 f3 ht₂ with h' | h' | h'
        · exact Or.inl (Finset.mem_erase.mpr ⟨hne1, h'⟩)
        · exact Or.inr (Or.inl (Finset.mem_erase.mpr ⟨hne2, h'⟩))
        · exact Or.inr (Or.inr (Finset.mem_erase.mpr ⟨hne3, h'⟩))
      obtain ⟨α', β', L', hreach, hpr', hc1, hc2, hlift⟩ :=
        ih _ _ _ (Q.erase q₀) (by rw [Finset.card_erase_of_mem hq₀Q]; omega) h₁ hb₁ hconn₁ htri₁
          (by omega)
      refine ⟨α', β', L', Relation.ReflTransGen.head hstep hreach, hpr', by omega, by omega,
        fun 𝒳' hfol' => ?_⟩
      obtain ⟨𝒳₁, hfol₁, hw₁⟩ := hlift 𝒳' hfol'
      obtain ⟨𝒳, hfol, hw⟩ := ep_fol_tri_lift α β L x y z e1 e2 e3 h ht hTcut 𝒳₁ hfol₁
      exact ⟨𝒳, hfol, hw₁.trans hw⟩

/-- Profile of an edge with respect to a vertex set `X`: whether it touches `X`, that it is not
inside `X`, and which singletons of `X` it crosses. -/
def EpProf {W E : Type*} (α β : E → W) (X : Finset W) (g : E) (t : Prop) (f : W → Prop) : Prop :=
  ((α g ∈ X ∨ β g ∈ X) ↔ t) ∧ ¬(α g ∈ X ∧ β g ∈ X) ∧ ∀ v ∈ X, (epCross α β {v} g ↔ f v)

lemma ep_prof_combine {W E : Type*} (α β α' β' : E → W) (X : Finset W) (g g' : E)
    (t t' : Prop) (f f' : W → Prop) (h1 : EpProf α β X g t f) (h2 : EpProf α' β' X g' t' f')
    (ht : t ↔ t') (hf : ∀ v ∈ X, (f v ↔ f' v)) :
    ((α' g' ∈ X ∨ β' g' ∈ X) ↔ (α g ∈ X ∨ β g ∈ X)) ∧
      ((α' g' ∈ X ∧ β' g' ∈ X) ↔ (α g ∈ X ∧ β g ∈ X)) ∧
      ∀ v ∈ X, (epCross α' β' {v} g' ↔ epCross α β {v} g) :=
  ⟨h2.1.trans (ht.symm.trans h1.1.symm),
    ⟨fun h' => absurd h' h2.2.1, fun h' => absurd h' h1.2.1⟩,
    fun v hv => (h2.2.2 v hv).trans ((hf v hv).symm.trans (h1.2.2 v hv).symm)⟩

/-- An edge with both ends outside `X`. -/
lemma ep_prof_out {W E : Type*} (α β : E → W) (X : Finset W) (g : E) (ha : α g ∉ X)
    (hb : β g ∉ X) : EpProf α β X g False (fun _ => False) := by
  refine ⟨⟨fun h' => h'.elim ha hb, fun h' => h'.elim⟩, fun h' => ha h'.1, fun v hv => ?_⟩
  rw [epCross_singleton]
  exact ⟨fun h' => h'.elim (fun h'' => ha (h''.1 ▸ hv)) (fun h'' => hb (h''.2 ▸ hv)),
    fun h' => h'.elim⟩

/-- An edge joining a vertex `s` outside `X` to a vertex `t`. -/
lemma ep_prof_one {W E : Type*} (α β : E → W) (X : Finset W) (g : E) (s t : W) (hs : s ∉ X)
    (h : (α g = s ∧ β g = t) ∨ (α g = t ∧ β g = s)) :
    EpProf α β X g (t ∈ X) (fun v => v = t) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨by rw [h1, h2]; exact ⟨fun h' => h'.elim (fun h'' => absurd h'' hs) id, Or.inr⟩,
      by rw [h1]; exact fun h' => hs h'.1, fun v hv => ?_⟩
    rw [epCross_singleton, h1, h2]
    exact ⟨fun h' => h'.elim (fun h'' => absurd (h''.1 ▸ hv) hs) (fun h'' => h''.2.symm),
      fun h' => Or.inr ⟨fun h'' => hs (h'' ▸ hv), h'.symm⟩⟩
  · refine ⟨by rw [h1, h2]; exact ⟨fun h' => h'.elim id (fun h'' => absurd h'' hs), Or.inl⟩,
      by rw [h2]; exact fun h' => hs h'.2, fun v hv => ?_⟩
    rw [epCross_singleton, h1, h2]
    exact ⟨fun h' => h'.elim (fun h'' => h''.1.symm) (fun h'' => absurd (h''.2 ▸ hv) hs),
      fun h' => Or.inl ⟨h'.symm, fun h'' => hs (h'' ▸ hv)⟩⟩

lemma ep_two_swaps {E : Type*} [DecidableEq E] (a b c d : E) (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (B D : Prop) [Decidable B]
    [Decidable D] :
    ∃ σ : E ≃ E, σ a = (if B then b else a) ∧ σ b = (if B then a else b) ∧
      σ c = (if D then d else c) ∧ σ d = (if D then c else d) ∧
      ∀ g, g ≠ a → g ≠ b → g ≠ c → g ≠ d → σ g = g := by
  by_cases hB : B <;> by_cases hD : D
  · refine ⟨(Equiv.swap a b).trans (Equiv.swap c d), ?_, ?_, ?_, ?_, fun g h1 h2 h3 h4 => ?_⟩
    · rw [if_pos hB, Equiv.trans_apply, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hbc hbd]
    · rw [if_pos hB, Equiv.trans_apply, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hac had]
    · rw [if_pos hD, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm,
        Equiv.swap_apply_left]
    · rw [if_pos hD, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne had.symm hbd.symm,
        Equiv.swap_apply_right]
    · rw [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.swap_apply_of_ne_of_ne h3 h4]
  · refine ⟨Equiv.swap a b, ?_, ?_, ?_, ?_, fun g h1 h2 h3 h4 => ?_⟩
    · rw [if_pos hB, Equiv.swap_apply_left]
    · rw [if_pos hB, Equiv.swap_apply_right]
    · rw [if_neg hD, Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm]
    · rw [if_neg hD, Equiv.swap_apply_of_ne_of_ne had.symm hbd.symm]
    · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
  · refine ⟨Equiv.swap c d, ?_, ?_, ?_, ?_, fun g h1 h2 h3 h4 => ?_⟩
    · rw [if_neg hB, Equiv.swap_apply_of_ne_of_ne hac had]
    · rw [if_neg hB, Equiv.swap_apply_of_ne_of_ne hbc hbd]
    · rw [if_pos hD, Equiv.swap_apply_left]
    · rw [if_pos hD, Equiv.swap_apply_right]
    · rw [Equiv.swap_apply_of_ne_of_ne h3 h4]
  · exact ⟨Equiv.refl E, by rw [if_neg hB]; rfl, by rw [if_neg hB]; rfl, by rw [if_neg hD]; rfl,
      by rw [if_neg hD]; rfl, fun _ _ _ _ _ => rfl⟩

set_option maxHeartbeats 1600000 in
open Classical in
/-- **Lemma 23(3), one burl.** A burl of the split multigraph that contains neither the outer
end of `a` nor the outer end of `c` is a burl of `G` with a cut of the same size. -/
theorem epSp_burl {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (p q : W)
    (a b c d m : E) (h : EpCubicD α β L) (hp : EpPath4 α β L p q a b c d m) (X : Finset W)
    (hXL : X ⊆ L \ {p, q}) (haX : epOut α β {p, q} a ∉ X) (hcX : epOut α β {p, q} c ∉ X)
    (hburl : EpBurl (epSpA α β p q a b c d) (epSpB α β p q a b c d) X) :
    EpBurl α β X ∧
      (epCut α β X).card = (epCut (epSpA α β p q a b c d) (epSpB α β p q a b c d) X).card := by
  obtain ⟨he1, he2, hm⟩ := hp.ends
  have hnl : ∀ g, α g ∈ L → α g ≠ β g := by
    intro g hg
    rcases h.1 g with h' | h'
    · exact h'.2.2
    · exact absurd hg h'.1
  have hlv : ∀ g, β g ∈ L → α g ∈ L := by
    intro g hg
    rcases h.1 g with h' | h'
    · exact h'.1
    · exact absurd (h'.2 ▸ hg) h'.1
  have htouch := hp.touch hnl hlv
  obtain ⟨hpL, hqL, hpq, hsp, hsq, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ := hp
  have hmem : ∀ w, w ∈ ({p, q} : Finset W) ↔ w = p ∨ w = q := by
    intro w; simp only [Finset.mem_insert, Finset.mem_singleton]
  have hpX : p ∉ X := fun h' => (Finset.mem_sdiff.mp (hXL h')).2 ((hmem p).mpr (Or.inl rfl))
  have hqX : q ∉ X := fun h' => (Finset.mem_sdiff.mp (hXL h')).2 ((hmem q).mpr (Or.inr rfl))
  obtain ⟨oa, hoa⟩ : ∃ oa, oa = epOut α β {p, q} a := ⟨_, rfl⟩
  obtain ⟨ob, hob⟩ : ∃ ob, ob = epOut α β {p, q} b := ⟨_, rfl⟩
  obtain ⟨oc, hoc⟩ : ∃ oc, oc = epOut α β {p, q} c := ⟨_, rfl⟩
  obtain ⟨od, hod⟩ : ∃ od, od = epOut α β {p, q} d := ⟨_, rfl⟩
  rw [← hoa] at haX
  rw [← hoc] at hcX
  have ha := (he1 a (Or.inl rfl)).2
  have hc := (he1 c (Or.inr rfl)).2
  have hb := (he2 b (Or.inl rfl)).2
  have hd := (he2 d (Or.inr rfl)).2
  rw [← hoa] at ha
  rw [← hoc] at hc
  rw [← hob] at hb
  rw [← hod] at hd
  -- ends in the split multigraph
  have hA'a : epSpA α β p q a b c d a = oa ∧ epSpB α β p q a b c d a = ob := by
    unfold epSpA epSpB; rw [if_pos rfl, if_pos rfl]; exact ⟨hoa.symm, hob.symm⟩
  have hA'c : epSpA α β p q a b c d c = oc ∧ epSpB α β p q a b c d c = od := by
    unfold epSpA epSpB
    rw [if_neg d1.symm, if_neg d1.symm, if_pos rfl, if_pos rfl]; exact ⟨hoc.symm, hod.symm⟩
  have hdead : ∀ g, g ≠ a → g ≠ c → (α g ∈ ({p, q} : Finset W) ∨ β g ∈ ({p, q} : Finset W)) →
      epSpA α β p q a b c d g = p ∧ epSpB α β p q a b c d g = p := by
    intro g hga hgc ht
    unfold epSpA epSpB
    rw [if_neg hga, if_neg hga, if_neg hgc, if_neg hgc, if_pos ht, if_pos ht]
    exact ⟨rfl, rfl⟩
  have hsame : ∀ g, g ≠ a → g ≠ c → ¬(α g ∈ ({p, q} : Finset W) ∨ β g ∈ ({p, q} : Finset W)) →
      epSpA α β p q a b c d g = α g ∧ epSpB α β p q a b c d g = β g := by
    intro g hga hgc ht
    unfold epSpA epSpB
    rw [if_neg hga, if_neg hga, if_neg hgc, if_neg hgc, if_neg ht, if_neg ht]
    exact ⟨rfl, rfl⟩
  -- profiles
  have Ga : EpProf α β X a False (fun _ => False) := by
    rcases ha with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact ep_prof_out α β X a (e1 ▸ hpX) (e2 ▸ haX)
    · exact ep_prof_out α β X a (e1 ▸ haX) (e2 ▸ hpX)
  have Gc : EpProf α β X c False (fun _ => False) := by
    rcases hc with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact ep_prof_out α β X c (e1 ▸ hpX) (e2 ▸ hcX)
    · exact ep_prof_out α β X c (e1 ▸ hcX) (e2 ▸ hpX)
  have Gm : EpProf α β X m False (fun _ => False) := by
    rcases hm with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact ep_prof_out α β X m (e1 ▸ hpX) (e2 ▸ hqX)
    · exact ep_prof_out α β X m (e1 ▸ hqX) (e2 ▸ hpX)
  have Gb : EpProf α β X b (ob ∈ X) (fun v => v = ob) := ep_prof_one α β X b q ob hqX hb
  have Gd : EpProf α β X d (od ∈ X) (fun v => v = od) := ep_prof_one α β X d q od hqX hd
  have G'a : EpProf (epSpA α β p q a b c d) (epSpB α β p q a b c d) X a (ob ∈ X)
      (fun v => v = ob) := ep_prof_one _ _ X a oa ob haX (Or.inl hA'a)
  have G'c : EpProf (epSpA α β p q a b c d) (epSpB α β p q a b c d) X c (od ∈ X)
      (fun v => v = od) := ep_prof_one _ _ X c oc od hcX (Or.inl hA'c)
  have G'dead : ∀ g, g ≠ a → g ≠ c → (α g ∈ ({p, q} : Finset W) ∨ β g ∈ ({p, q} : Finset W)) →
      EpProf (epSpA α β p q a b c d) (epSpB α β p q a b c d) X g False (fun _ => False) := by
    intro g hga hgc ht
    obtain ⟨k1, k2⟩ := hdead g hga hgc ht
    exact ep_prof_out _ _ X g (by rw [k1]; exact hpX) (by rw [k2]; exact hpX)
  have tb := (htouch b).mpr (Or.inr (Or.inl rfl))
  have td := (htouch d).mpr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have tm := (htouch m).mpr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  obtain ⟨σ, sa, sb, sc, sd, srest⟩ := ep_two_swaps a b c d d7 d1 d8 d9.symm d4 d10 (ob ∈ X) (od ∈ X)
  have hP : ∀ g, ((epSpA α β p q a b c d (σ g) ∈ X ∨ epSpB α β p q a b c d (σ g) ∈ X) ↔
        (α g ∈ X ∨ β g ∈ X)) ∧
      ((epSpA α β p q a b c d (σ g) ∈ X ∧ epSpB α β p q a b c d (σ g) ∈ X) ↔
        (α g ∈ X ∧ β g ∈ X)) ∧
      ∀ v ∈ X, (epCross (epSpA α β p q a b c d) (epSpB α β p q a b c d) {v} (σ g) ↔
        epCross α β {v} g) := by
    intro g
    by_cases hga : g = a
    · rw [hga, sa]
      by_cases hB : ob ∈ X
      · rw [if_pos hB]
        exact ep_prof_combine α β _ _ X a b _ _ _ _ Ga (G'dead b d7.symm d9.symm tb) Iff.rfl
          (fun _ _ => Iff.rfl)
      · rw [if_neg hB]
        exact ep_prof_combine α β _ _ X a a _ _ _ _ Ga G'a
          ⟨fun h' => h'.elim, fun h' => hB h'⟩ (fun v hv => ⟨fun h' => h'.elim,
            fun h' => hB (h' ▸ hv)⟩)
    · by_cases hgb : g = b
      · rw [hgb, sb]
        by_cases hB : ob ∈ X
        · rw [if_pos hB]
          exact ep_prof_combine α β _ _ X b a _ _ _ _ Gb G'a Iff.rfl (fun _ _ => Iff.rfl)
        · rw [if_neg hB]
          exact ep_prof_combine α β _ _ X b b _ _ _ _ Gb (G'dead b d7.symm d9.symm tb)
            ⟨fun h' => hB h', fun h' => h'.elim⟩ (fun v hv => ⟨fun h' => hB (h' ▸ hv),
              fun h' => h'.elim⟩)
      · by_cases hgc : g = c
        · rw [hgc, sc]
          by_cases hD : od ∈ X
          · rw [if_pos hD]
            exact ep_prof_combine α β _ _ X c d _ _ _ _ Gc (G'dead d d8.symm d10.symm td) Iff.rfl
              (fun _ _ => Iff.rfl)
          · rw [if_neg hD]
            exact ep_prof_combine α β _ _ X c c _ _ _ _ Gc G'c
              ⟨fun h' => h'.elim, fun h' => hD h'⟩ (fun v hv => ⟨fun h' => h'.elim,
                fun h' => hD (h' ▸ hv)⟩)
        · by_cases hgd : g = d
          · rw [hgd, sd]
            by_cases hD : od ∈ X
            · rw [if_pos hD]
              exact ep_prof_combine α β _ _ X d c _ _ _ _ Gd G'c Iff.rfl (fun _ _ => Iff.rfl)
            · rw [if_neg hD]
              exact ep_prof_combine α β _ _ X d d _ _ _ _ Gd (G'dead d d8.symm d10.symm td)
                ⟨fun h' => hD h', fun h' => h'.elim⟩ (fun v hv => ⟨fun h' => hD (h' ▸ hv),
                  fun h' => h'.elim⟩)
          · rw [srest g hga hgb hgc hgd]
            by_cases ht : α g ∈ ({p, q} : Finset W) ∨ β g ∈ ({p, q} : Finset W)
            · have hgm : g = m := by
                rcases (htouch g).mp ht with e | e | e | e | e
                · exact absurd e hga
                · exact absurd e hgb
                · exact absurd e hgc
                · exact absurd e hgd
                · exact e
              rw [hgm]
              exact ep_prof_combine α β _ _ X m m _ _ _ _ Gm (G'dead m d2.symm d3.symm tm) Iff.rfl
                (fun _ _ => Iff.rfl)
            · obtain ⟨k1, k2⟩ := hsame g hga hgc ht
              refine ⟨by rw [k1, k2], by rw [k1, k2], fun v _ => ?_⟩
              rw [epCross_singleton, epCross_singleton, k1, k2]
  have hXL' : X ⊆ L := hXL.trans Finset.sdiff_subset
  refine ⟨ep_burl_transfer α β _ _ X σ (fun e he => hnl e (hXL' he))
    (fun g v hv => (hP g).2.2 v hv) (fun g => (hP g).1) (fun g => (hP g).2.1) hburl,
    ep_cut_card_transfer α β _ _ X σ (fun g => (hP g).1) (fun g => (hP g).2.1)⟩

open Classical in
/-- Dropping the members of a rootless foliage that contain a given vertex loses at most `β₁`. -/
lemma ep_fol0_drop {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (𝒳 : Finset (Finset W)) (hfol : EpFol0 α β L 𝒳) (v : W) :
    EpFol0 α β L (𝒳.filter (fun X => v ∉ X)) ∧
      epFw α β 𝒳 - 196 / 995 ≤ epFw α β (𝒳.filter (fun X => v ∉ X)) := by
  refine ⟨⟨fun X hX => hfol.1 X (Finset.mem_of_mem_filter X hX), fun X hX X' hX' hne =>
    hfol.2 X (Finset.mem_of_mem_filter X hX) X' (Finset.mem_of_mem_filter X' hX') hne⟩, ?_⟩
  unfold epFw
  rw [← Finset.sum_filter_add_sum_filter_not 𝒳 (fun X => v ∉ X)]
  have hcard : (𝒳.filter (fun X => ¬v ∉ X)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro X hX X' hX'
    rw [Finset.mem_filter, not_not] at hX hX'
    by_contra hne
    exact Finset.disjoint_left.mp (hfol.2 X hX.1 X' hX'.1 hne) hX.2 hX'.2
  have hle : ∑ X ∈ 𝒳.filter (fun X => ¬v ∉ X),
      (if EpTwig α β X then (196 : ℝ) / 995 else 98 / 995) ≤ 196 / 995 := by
    calc _ ≤ ∑ X ∈ 𝒳.filter (fun X => ¬v ∉ X), (196 : ℝ) / 995 :=
          Finset.sum_le_sum (fun X _ => by split_ifs <;> norm_num)
      _ = ((𝒳.filter (fun X => ¬v ∉ X)).card : ℝ) * (196 / 995) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 1 * (196 / 995) := by
          apply mul_le_mul_of_nonneg_right _ (by norm_num)
          exact_mod_cast hcard
      _ = 196 / 995 := one_mul _
  linarith

open Classical in
/-- **Lemma 23(3).** A foliage of the split multigraph gives a foliage of `G` with a loss of at
most `2 β₁`. -/
theorem epSp_fol {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (p q : W)
    (a b c d m : E) (h : EpCubicD α β L) (hp : EpPath4 α β L p q a b c d m)
    (𝒳' : Finset (Finset W))
    (hfol : EpFol0 (epSpA α β p q a b c d) (epSpB α β p q a b c d) (L \ {p, q}) 𝒳') :
    ∃ 𝒳, EpFol0 α β L 𝒳 ∧
      epFw (epSpA α β p q a b c d) (epSpB α β p q a b c d) 𝒳' - 2 * (196 / 995) ≤ epFw α β 𝒳 := by
  obtain ⟨f1, w1⟩ := ep_fol0_drop _ _ _ 𝒳' hfol (epOut α β {p, q} a)
  obtain ⟨f2, w2⟩ := ep_fol0_drop _ _ _ _ f1 (epOut α β {p, q} c)
  have hmem : ∀ X ∈ (𝒳'.filter (fun X => epOut α β {p, q} a ∉ X)).filter
      (fun X => epOut α β {p, q} c ∉ X), EpBurl α β X ∧
      (epCut α β X).card = (epCut (epSpA α β p q a b c d) (epSpB α β p q a b c d) X).card := by
    intro X hX
    obtain ⟨hX1, hcX⟩ := Finset.mem_filter.mp hX
    obtain ⟨hX2, haX⟩ := Finset.mem_filter.mp hX1
    exact epSp_burl α β L p q a b c d m h hp X (hfol.1 X hX2).1 haX hcX (hfol.1 X hX2).2
  refine ⟨_, ⟨fun X hX => ⟨((f2.1 X hX).1).trans Finset.sdiff_subset, (hmem X hX).1⟩, f2.2⟩, ?_⟩
  have heq : epFw α β ((𝒳'.filter (fun X => epOut α β {p, q} a ∉ X)).filter
      (fun X => epOut α β {p, q} c ∉ X)) =
      epFw (epSpA α β p q a b c d) (epSpB α β p q a b c d)
        ((𝒳'.filter (fun X => epOut α β {p, q} a ∉ X)).filter
          (fun X => epOut α β {p, q} c ∉ X)) := by
    unfold epFw
    refine Finset.sum_congr rfl fun X hX => ?_
    have : EpTwig α β X ↔ EpTwig (epSpA α β p q a b c d) (epSpB α β p q a b c d) X := by
      unfold EpTwig; rw [(hmem X hX).2]
    by_cases ht : EpTwig α β X
    · rw [if_pos ht, if_pos (this.mp ht)]
    · rw [if_neg ht, if_neg (fun h' => ht (this.mpr h'))]
  rw [heq]
  linarith

/-- The statement of Lemma 13 for one multigraph: for every upper bound `F` of the weights of
its foliages, every edge is in at least `2 ^ (α |L| − F + γ)` perfect matchings. -/
def EpL13 {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) : Prop :=
  ∀ F : ℝ, (∀ 𝒳, EpFol0 α β L 𝒳 → epFw α β 𝒳 ≤ F) → ∀ g, α g ∈ L →
    (2 : ℝ) ^ ((L.card : ℝ) / 995 - F + 396 / 995) ≤ (epMe α β L g : ℝ)

lemma ep_fw_bound_nonneg {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (F : ℝ)
    (hF : ∀ 𝒳, EpFol0 α β L 𝒳 → epFw α β 𝒳 ≤ F) : 0 ≤ F := by
  classical
  have := hF ∅ ⟨fun X hX => absurd hX (Finset.notMem_empty X),
    fun X hX => absurd hX (Finset.notMem_empty X)⟩
  unfold epFw at this
  rw [Finset.sum_empty] at this
  exact this

lemma EpFol.toFol0 {W E : Type*} [Fintype E] {α β : E → W} {L : Finset W} {r : W}
    {𝒳 : Finset (Finset W)} (h : EpFol α β L r 𝒳) : EpFol0 α β L 𝒳 :=
  ⟨fun X hX => ⟨(h.1 X hX).1, (h.1 X hX).2.2⟩, h.2⟩

/-- If the exponent is at most one, two perfect matchings through every edge suffice. -/
lemma ep_l13_of_two {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (F : ℝ) (g : E)
    (hx : (L.card : ℝ) / 995 - F + 396 / 995 ≤ 1) (h2 : 2 ≤ epMe α β L g) :
    (2 : ℝ) ^ ((L.card : ℝ) / 995 - F + 396 / 995) ≤ (epMe α β L g : ℝ) := by
  have h1 : (2 : ℝ) ^ ((L.card : ℝ) / 995 - F + 396 / 995) ≤ (2 : ℝ) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hx
  rw [Real.rpow_one] at h1
  have h3 : (2 : ℝ) ≤ (epMe α β L g : ℝ) := by exact_mod_cast h2
  linarith

set_option maxHeartbeats 1600000 in
open Classical in
/-- **One split in Case 1 of Lemma 13.** For a path in a cyclically 4-edge-connected
multigraph and an edge `e` at its first vertex: either `G` has a heavy foliage, or the number
of perfect matchings containing `e` and avoiding `b` is bounded below by the induction
hypothesis applied to the pruned split multigraph. -/
theorem ep_split_package {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (p q : W)
    (a b c d m : E) (h : EpCubicD α β L) (h4 : EpCyc4 α β L) (h12 : 12 ≤ L.card)
    (hp : EpPath4 α β L p q a b c d m)
    (hab : epOut α β {p, q} a ≠ epOut α β {p, q} b)
    (hcd : epOut α β {p, q} c ≠ epOut α β {p, q} d) (e : E) (heL : α e ∈ L)
    (het : ¬(α e ∈ ({p, q} : Finset W) ∨ β e ∈ ({p, q} : Finset W)))
    (hecr : epCross α β {epOut α β {p, q} a} e)
    (IH : ∀ (α₁ β₁ : E → W) (L₁ : Finset W), L₁.card < L.card → EpCubicD α₁ β₁ L₁ →
      EpBridgeless α₁ β₁ L₁ → EpConnected α₁ β₁ L₁ → EpPruned α₁ β₁ L₁ → EpHasCore α₁ β₁ L₁ →
      EpL13 α₁ β₁ L₁) :
    (∃ 𝒳, EpFol0 α β L 𝒳 ∧
      ((L.card : ℝ) - 6) / 995 + 98 / 995 - 2 * (196 / 995) ≤ epFw α β 𝒳) ∨
    (∀ F : ℝ, (∀ 𝒳, EpFol0 α β L 𝒳 → epFw α β 𝒳 ≤ F) →
      (2 : ℝ) ^ (((L.card : ℝ) - 6) / 995 - (F + 2 * (196 / 995)) + 396 / 995) ≤
        (((epPMs α β L).filter (fun M => e ∈ M ∧ b ∉ M)).card : ℝ)) := by
  have h' := epSp_cubic α β L p q a b c d m h hp hab hcd
  have hpqL : ({p, q} : Finset W) ⊆ L := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hp.1
    · rw [Finset.mem_singleton.mp hw]; exact hp.2.1
  have hcardL' : (L \ ({p, q} : Finset W)).card + 2 = L.card := by
    have := Finset.card_sdiff_add_card_eq_card hpqL
    rw [Finset.card_pair hp.2.2.1] at this
    exact this
  have hcut2 := epSp_cut_ge_two α β L p q a b c d m h h4 hp hab hcd
  have hempty : ∀ T : Finset W, T = ∅ ∨ T = L \ ({p, q} : Finset W) →
      epCut (epSpA α β p q a b c d) (epSpB α β p q a b c d) T = ∅ := by
    intro T hT
    rw [Finset.eq_empty_iff_forall_notMem]
    intro g hg
    rw [mem_epCut] at hg
    unfold epCross at hg
    rcases hT with rfl | rfl
    · simp at hg
    · rcases h'.1 g with ⟨l1, l2, -⟩ | ⟨l1, l2⟩
      · exact hg.elim (fun h'' => h''.2 l2) (fun h'' => h''.1 l1)
      · rw [l2] at hg
        exact hg.elim (fun h'' => h''.2 h''.1) (fun h'' => h''.1 h''.2)
  have hb' : EpBridgeless (epSpA α β p q a b c d) (epSpB α β p q a b c d) (L \ {p, q}) := by
    intro T hT h1
    by_cases hTe : T = ∅ ∨ T = L \ ({p, q} : Finset W)
    · rw [hempty T hTe, Finset.card_empty] at h1
      exact absurd h1 (by norm_num)
    · push_neg at hTe
      have := hcut2 T hT hTe.1 hTe.2
      omega
  have hconn' : EpConnected (epSpA α β p q a b c d) (epSpB α β p q a b c d) (L \ {p, q}) := by
    intro T hT hne hneL h0
    have := hcut2 T hT hne hneL
    rw [h0, Finset.card_empty] at this
    omega
  have hnotri := ep_cyc4_no_triangle α β L h h4 (by omega)
  have hac : a ≠ c := hp.2.2.2.2.2.1
  obtain ⟨α'', β'', L'', hreach, hpr, hc1, hc2, hlift⟩ :=
    ep_prune_budget 2 (epSpA α β p q a b c d) (epSpB α β p q a b c d) (L \ {p, q}) {a, c}
      (Finset.card_pair hac) h' hb' hconn'
      (fun x y z e1 e2 e3 ht => by
        have := epSp_triangle_new α β L p q a b c d m hac hnotri x y z e1 e2 e3 ht
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact this)
      (by omega)
  obtain ⟨h'', hb'', hconn'', -⟩ := hreach.preserves h' hb' hconn'
  -- lifting foliages from the pruned split multigraph to `G`
  have hlift2 : ∀ 𝒳'', EpFol0 α'' β'' L'' 𝒳'' → ∃ 𝒳, EpFol0 α β L 𝒳 ∧
      epFw α'' β'' 𝒳'' - 2 * (196 / 995) ≤ epFw α β 𝒳 := by
    intro 𝒳'' hfol''
    obtain ⟨𝒳', hfol', hw'⟩ := hlift 𝒳'' hfol''
    obtain ⟨𝒳, hfol, hw⟩ := epSp_fol α β L p q a b c d m h hp 𝒳' hfol'
    exact ⟨𝒳, hfol, by linarith⟩
  by_cases hcore : EpHasCore α'' β'' L''
  · right
    intro F hF
    have hF'' : ∀ 𝒳'', EpFol0 α'' β'' L'' 𝒳'' → epFw α'' β'' 𝒳'' ≤ F + 2 * (196 / 995) := by
      intro 𝒳'' hfol''
      obtain ⟨𝒳, hfol, hw⟩ := hlift2 𝒳'' hfol''
      have := hF 𝒳 hfol
      linarith
    have hih := IH α'' β'' L'' (by omega) h'' hb'' hconn'' hpr hcore _ hF''
    have hk : ∀ g, α'' g ∈ L'' →
        ⌈(2 : ℝ) ^ (((L.card : ℝ) - 6) / 995 - (F + 2 * (196 / 995)) + 396 / 995)⌉₊ ≤
          epMe α'' β'' L'' g := by
      intro g hg
      apply Nat.ceil_le.mpr
      refine le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_) (hih g hg)
      have : (L.card : ℝ) ≤ L''.card + 6 := by exact_mod_cast (by omega : L.card ≤ L''.card + 6)
      linarith
    have he' : epSpA α β p q a b c d e ∈ L \ ({p, q} : Finset W) := by
      have hea : e ≠ a := by
        intro h''e
        obtain ⟨he1, -, -⟩ := hp.ends
        rcases (he1 a (Or.inl rfl)).2 with ⟨e1, -⟩ | ⟨-, e2⟩
        · exact het (Or.inl (by rw [h''e, e1]; exact Finset.mem_insert_self _ _))
        · exact het (Or.inr (by rw [h''e, e2]; exact Finset.mem_insert_self _ _))
      have hec : e ≠ c := by
        intro h''e
        obtain ⟨he1, -, -⟩ := hp.ends
        rcases (he1 c (Or.inr rfl)).2 with ⟨e1, -⟩ | ⟨-, e2⟩
        · exact het (Or.inl (by rw [h''e, e1]; exact Finset.mem_insert_self _ _))
        · exact het (Or.inr (by rw [h''e, e2]; exact Finset.mem_insert_self _ _))
      unfold epSpA
      rw [if_neg hea, if_neg hec, if_neg het]
      exact Finset.mem_sdiff.mpr ⟨heL, fun h''' => het (Or.inl h''')⟩
    have hk' := EpReach.mstar_le hreach h' hb' hconn' _ hk e he'
    have hcount := epSp_count α β L p q a b c d m h hp hab hcd e het hecr
    have h1 : (⌈(2 : ℝ) ^ (((L.card : ℝ) - 6) / 995 - (F + 2 * (196 / 995)) + 396 / 995)⌉₊ : ℝ) ≤
        (((epPMs α β L).filter (fun M => e ∈ M ∧ b ∉ M)).card : ℝ) := by
      exact_mod_cast hk'.trans hcount
    exact (Nat.le_ceil _).trans h1
  · left
    obtain ⟨v, hv⟩ : L''.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨𝒳'', hfol'', hw''⟩ := ep_cor12 α'' β'' L'' v h'' hb'' hconn'' hv hcore hpr (by omega)
    obtain ⟨𝒳, hfol, hw⟩ := hlift2 𝒳'' hfol''.toFol0
    refine ⟨𝒳, hfol, ?_⟩
    have : (L.card : ℝ) ≤ L''.card + 6 := by exact_mod_cast (by omega : L.card ≤ L''.card + 6)
    linarith

lemma EpPath4.swap {W E : Type*} {α β : E → W} {L : Finset W} {p q : W} {a b c d m : E}
    (hp : EpPath4 α β L p q a b c d m) : EpPath4 α β L p q a d c b m := by
  obtain ⟨hpL, hqL, hpq, hsp, hsq, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ := hp
  exact ⟨hpL, hqL, hpq, hsp, fun g => by rw [hsq]; tauto, d1, d2, d3, d4.symm, d6, d5, d8, d7,
    d10, d9⟩

open Classical in
/-- In a path configuration of a triangle-free multigraph the outer ends of `a`, `b` are
different, and so are those of `c`, `d`. -/
lemma EpPath4.outer_ne {W E : Type*} {α β : E → W} {L : Finset W} {p q : W} {a b c d m : E}
    (hp : EpPath4 α β L p q a b c d m) (h : ∀ g, α g ≠ β g → α g ∈ L ∧ β g ∈ L)
    (hnotri : ∀ x y z e1 e2 e3, ¬EpTriangle α β L x y z e1 e2 e3) :
    epOut α β {p, q} a ≠ epOut α β {p, q} b ∧ epOut α β {p, q} c ≠ epOut α β {p, q} d := by
  obtain ⟨he1, he2, hm⟩ := hp.ends
  obtain ⟨hpL, hqL, hpq, -⟩ := hp
  have hmem : ∀ w, w ∈ ({p, q} : Finset W) ↔ w = p ∨ w = q := by
    intro w; simp only [Finset.mem_insert, Finset.mem_singleton]
  have key : ∀ g g', (g = a ∨ g = c) → (g' = b ∨ g' = d) →
      epOut α β {p, q} g ≠ epOut α β {p, q} g' := by
    intro g g' hg hg' heq
    obtain ⟨n1, e1⟩ := he1 g hg
    obtain ⟨n2, e2⟩ := he2 g' hg'
    have hop : epOut α β {p, q} g ≠ p := fun h' => n1 ((hmem _).mpr (Or.inl h'))
    have hoq : epOut α β {p, q} g ≠ q := fun h' => n1 ((hmem _).mpr (Or.inr h'))
    rw [← heq] at e2
    have hoL : epOut α β {p, q} g ∈ L := by
      rcases e1 with ⟨x1, x2⟩ | ⟨x1, x2⟩
      · exact x2 ▸ (h g (by rw [x1, x2]; exact hop.symm)).2
      · exact x1 ▸ (h g (by rw [x1, x2]; exact hop)).1
    refine hnotri (epOut α β {p, q} g) p q g m g' ⟨hoL, hpL, hqL, hop, hpq, hoq, ?_, ?_, ?_⟩
    · intro w
      exact ep_edge_cross α β _ p g hop (e1.elim Or.inr Or.inl) w
    · intro w
      exact ep_edge_cross α β p q m hpq hm w
    · intro w
      exact ep_edge_cross α β q _ g' hoq.symm e2 w
  exact ⟨key a b (Or.inl rfl) (Or.inl rfl), key c d (Or.inr rfl) (Or.inr rfl)⟩

lemma ep_three_with {E : Type*} [DecidableEq E] (S : Finset E) (hS : S.card = 3) (f : E)
    (hf : f ∈ S) : ∃ g₁ g₂, f ≠ g₁ ∧ f ≠ g₂ ∧ g₁ ≠ g₂ ∧ ∀ g, g ∈ S ↔ g = f ∨ g = g₁ ∨ g = g₂ := by
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hS
  simp only [Finset.mem_insert, Finset.mem_singleton] at hf
  rcases hf with rfl | rfl | rfl
  · exact ⟨y, z, hxy, hxz, hyz, fun g => by simp only [Finset.mem_insert, Finset.mem_singleton]⟩
  · exact ⟨x, z, hxy.symm, hyz, hxz, fun g => by
      simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
  · exact ⟨x, y, hxz.symm, hyz.symm, hxy, fun g => by
      simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩

open Classical in
/-- No parallel edges in a cyclically 4-edge-connected multigraph with at least six vertices. -/
lemma ep_cyc4_no_parallel {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (h : EpCubicD α β L) (h4 : EpCyc4 α β L) (h6 : 6 ≤ L.card) (s t : W) (hs : s ∈ L)
    (ht : t ∈ L) (hst : s ≠ t) (g g' : E) (hg : epCross α β {s} g ∧ epCross α β {t} g)
    (hg' : epCross α β {s} g' ∧ epCross α β {t} g') : g = g' := by
  by_contra hne
  have hd : Disjoint ({s} : Finset W) {t} := Finset.disjoint_singleton.mpr hst
  have e1 := ep_cut_union α β {s} {t} hd
  rw [h.2 s hs, h.2 t ht] at e1
  have hb : ∀ f, epCross α β {s} f ∧ epCross α β {t} f → f ∈ epBtw α β {s} {t} := by
    intro f hf
    rw [mem_epBtw]
    simp only [Finset.mem_singleton]
    obtain ⟨a1, a2⟩ := hf
    rw [epCross_singleton] at a1 a2
    rcases a1 with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;> rcases a2 with ⟨c1, c2⟩ | ⟨c1, c2⟩
    · exact absurd (b1.symm.trans c1) hst
    · exact Or.inl ⟨b1, c2⟩
    · exact Or.inr ⟨c1, b2⟩
    · exact absurd (b2.symm.trans c2) hst
  have h2 : 2 ≤ (epBtw α β {s} {t}).card := by
    have : ({g, g'} : Finset E) ⊆ epBtw α β {s} {t} := by
      intro f hf
      rcases Finset.mem_insert.mp hf with rfl | hf
      · exact hb _ hg
      · rw [Finset.mem_singleton.mp hf]; exact hb _ hg'
    have := Finset.card_le_card this
    rw [Finset.card_pair hne] at this
    exact this
  have hsub : ({s} ∪ {t} : Finset W) ⊆ L :=
    Finset.union_subset (Finset.singleton_subset_iff.mpr hs) (Finset.singleton_subset_iff.mpr ht)
  have hcard : ({s} ∪ {t} : Finset W).card = 2 := by
    rw [Finset.card_union_of_disjoint hd, Finset.card_singleton, Finset.card_singleton]
  have := h4.1 _ hsub ⟨s, Finset.mem_union_left _ (Finset.mem_singleton_self s)⟩
    (fun h' => by rw [h'] at hcard; omega)
  omega

/-- Ends of an edge crossing a singleton. -/
lemma epD_other_end {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (h : EpCubicD α β L)
    (v : W) (g : E) (hg : epCross α β {v} g) :
    ∃ w, w ≠ v ∧ w ∈ L ∧ v ∈ L ∧ ((α g = v ∧ β g = w) ∨ (α g = w ∧ β g = v)) := by
  rw [epCross_singleton] at hg
  have hne : α g ≠ β g := by
    rcases hg with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · exact fun h' => a2 (h'.symm.trans a1)
    · exact fun h' => a1 (h'.trans a2)
  have hl : α g ∈ L ∧ β g ∈ L := by
    rcases h.1 g with h' | h'
    · exact ⟨h'.1, h'.2.1⟩
    · exact absurd h'.2.symm hne
  rcases hg with ⟨a1, a2⟩ | ⟨a1, a2⟩
  · exact ⟨β g, a2, hl.2, a1 ▸ hl.1, Or.inl ⟨a1, rfl⟩⟩
  · exact ⟨α g, a1, hl.1, a2 ▸ hl.2, Or.inr ⟨rfl, a2⟩⟩

set_option maxHeartbeats 1600000 in
open Classical in
/-- **Local structure for Case 1 of Lemma 13.** Around an edge `e` of a cyclically
4-edge-connected multigraph with at least six vertices there are four path configurations
with final edges `h₁, h₁', h₂, h₂'` such that every perfect matching containing `e` contains
one of these four edges. -/
theorem ep_cyc4_local {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (h : EpCubicD α β L) (h4 : EpCyc4 α β L) (h6 : 6 ≤ L.card) (e : E) (heL : α e ∈ L) :
    ∃ (w w₁ w₂ : W) (f g₁ g₂ h₁ h₁' h₂ h₂' : E),
      EpPath4 α β L w w₁ f h₁ g₂ h₁' g₁ ∧ EpPath4 α β L w w₂ f h₂ g₁ h₂' g₂ ∧
      ¬(α e ∈ ({w, w₁} : Finset W) ∨ β e ∈ ({w, w₁} : Finset W)) ∧
      ¬(α e ∈ ({w, w₂} : Finset W) ∨ β e ∈ ({w, w₂} : Finset W)) ∧
      epCross α β {epOut α β {w, w₁} f} e ∧ epCross α β {epOut α β {w, w₂} f} e ∧
      ∀ M, M ∈ epPM α β L → e ∈ M → h₁ ∈ M ∨ h₁' ∈ M ∨ h₂ ∈ M ∨ h₂' ∈ M := by
  have hnotri := ep_cyc4_no_triangle α β L h h4 h6
  have hnp := ep_cyc4_no_parallel α β L h h4 h6
  have hene : α e ≠ β e := by
    rcases h.1 e with h' | h'
    · exact h'.2.2
    · exact absurd heL h'.1
  have hbL : β e ∈ L := by
    rcases h.1 e with h' | h'
    · exact h'.2.1
    · exact absurd heL h'.1
  obtain ⟨v, hv⟩ : ∃ v, v = β e := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u, u = α e := ⟨_, rfl⟩
  rw [← hv] at hbL hene
  rw [← hu] at heL hene
  have hecr : ∀ t, epCross α β {t} e ↔ t = u ∨ t = v :=
    ep_edge_cross α β u v e hene (Or.inl ⟨hu.symm, hv.symm⟩)
  -- another edge at `v`
  obtain ⟨f, hf, hfe⟩ := Finset.exists_mem_ne (by rw [h.2 v hbL]; norm_num :
    1 < (epCut α β {v}).card) e
  rw [mem_epCut] at hf
  obtain ⟨w, hwv, hwL, -, hfends⟩ := epD_other_end α β L h v f hf
  have hfcr : ∀ t, epCross α β {t} f ↔ t = v ∨ t = w :=
    ep_edge_cross α β v w f hwv.symm hfends
  -- the edges at `w`
  obtain ⟨g₁, g₂, n1, n2, n3, hw3⟩ := ep_three_with _ (h.2 w hwL) f
    ((mem_epCut _ _ _ _).mpr ((hfcr w).mpr (Or.inr rfl)))
  simp only [mem_epCut] at hw3
  obtain ⟨w₁, hw₁w, hw₁L, -, hg₁ends⟩ := epD_other_end α β L h w g₁
    ((hw3 g₁).mpr (Or.inr (Or.inl rfl)))
  obtain ⟨w₂, hw₂w, hw₂L, -, hg₂ends⟩ := epD_other_end α β L h w g₂
    ((hw3 g₂).mpr (Or.inr (Or.inr rfl)))
  have hg₁cr : ∀ t, epCross α β {t} g₁ ↔ t = w ∨ t = w₁ :=
    ep_edge_cross α β w w₁ g₁ hw₁w.symm hg₁ends
  have hg₂cr : ∀ t, epCross α β {t} g₂ ↔ t = w ∨ t = w₂ :=
    ep_edge_cross α β w w₂ g₂ hw₂w.symm hg₂ends
  -- distinctness of the vertices
  have hvw₁ : v ≠ w₁ := fun h' => n1 (hnp w v hwL hbL hwv f g₁
    ⟨(hfcr w).mpr (Or.inr rfl), (hfcr v).mpr (Or.inl rfl)⟩
    ⟨(hg₁cr w).mpr (Or.inl rfl), (hg₁cr v).mpr (Or.inr h')⟩)
  have hvw₂ : v ≠ w₂ := fun h' => n2 (hnp w v hwL hbL hwv f g₂
    ⟨(hfcr w).mpr (Or.inr rfl), (hfcr v).mpr (Or.inl rfl)⟩
    ⟨(hg₂cr w).mpr (Or.inl rfl), (hg₂cr v).mpr (Or.inr h')⟩)
  have hw₁w₂ : w₁ ≠ w₂ := fun h' => n3 (hnp w w₁ hwL hw₁L hw₁w.symm g₁ g₂
    ⟨(hg₁cr w).mpr (Or.inl rfl), (hg₁cr w₁).mpr (Or.inr rfl)⟩
    ⟨(hg₂cr w).mpr (Or.inl rfl), (hg₂cr w₁).mpr (Or.inr h')⟩)
  have huw : u ≠ w := fun h' => hfe (hnp v w hbL hwL hwv.symm f e
    ⟨(hfcr v).mpr (Or.inl rfl), (hfcr w).mpr (Or.inr rfl)⟩
    ⟨(hecr v).mpr (Or.inr rfl), (hecr w).mpr (Or.inl h'.symm)⟩)
  have huw₁ : u ≠ w₁ := fun h' =>
    hnotri v w w₁ f g₁ e ⟨hbL, hwL, hw₁L, hwv.symm, hw₁w.symm, hvw₁, hfcr, hg₁cr,
      fun t => by rw [hecr, h']⟩
  have huw₂ : u ≠ w₂ := fun h' =>
    hnotri v w w₂ f g₂ e ⟨hbL, hwL, hw₂L, hwv.symm, hw₂w.symm, hvw₂, hfcr, hg₂cr,
      fun t => by rw [hecr, h']⟩
  -- the edges at `w₁` and `w₂`
  obtain ⟨h₁, h₁', m1, m2, m3, hw₁3⟩ := ep_three_with _ (h.2 w₁ hw₁L) g₁
    ((mem_epCut _ _ _ _).mpr ((hg₁cr w₁).mpr (Or.inr rfl)))
  obtain ⟨h₂, h₂', k1, k2, k3, hw₂3⟩ := ep_three_with _ (h.2 w₂ hw₂L) g₂
    ((mem_epCut _ _ _ _).mpr ((hg₂cr w₂).mpr (Or.inr rfl)))
  simp only [mem_epCut] at hw₁3 hw₂3
  -- an edge at `w` other than the middle edge does not cross the other vertex
  have hx₁ : ∀ X Y, epCross α β {w} X → X ≠ g₁ → epCross α β {w₁} Y → X ≠ Y := by
    intro X Y hX hXg hY hXY
    exact hXg (hnp w w₁ hwL hw₁L hw₁w.symm X g₁ ⟨hX, hXY ▸ hY⟩
      ⟨(hg₁cr w).mpr (Or.inl rfl), (hg₁cr w₁).mpr (Or.inr rfl)⟩)
  have hx₂ : ∀ X Y, epCross α β {w} X → X ≠ g₂ → epCross α β {w₂} Y → X ≠ Y := by
    intro X Y hX hXg hY hXY
    exact hXg (hnp w w₂ hwL hw₂L hw₂w.symm X g₂ ⟨hX, hXY ▸ hY⟩
      ⟨(hg₂cr w).mpr (Or.inl rfl), (hg₂cr w₂).mpr (Or.inr rfl)⟩)
  have cf := (hfcr w).mpr (Or.inr rfl)
  have cg₁ := (hg₁cr w).mpr (Or.inl rfl)
  have cg₂ := (hg₂cr w).mpr (Or.inl rfl)
  have ch₁ := (hw₁3 h₁).mpr (Or.inr (Or.inl rfl))
  have ch₁' := (hw₁3 h₁').mpr (Or.inr (Or.inr rfl))
  have ch₂ := (hw₂3 h₂).mpr (Or.inr (Or.inl rfl))
  have ch₂' := (hw₂3 h₂').mpr (Or.inr (Or.inr rfl))
  have hP1 : EpPath4 α β L w w₁ f h₁ g₂ h₁' g₁ :=
    ⟨hwL, hw₁L, hw₁w.symm, fun g => by rw [hw3]; tauto, fun g => by rw [hw₁3]; tauto,
      n2, n1, n3.symm, m3, m1.symm, m2.symm, hx₁ f h₁ cf n1 ch₁, hx₁ f h₁' cf n1 ch₁',
      hx₁ g₂ h₁ cg₂ n3.symm ch₁, hx₁ g₂ h₁' cg₂ n3.symm ch₁'⟩
  have hP2 : EpPath4 α β L w w₂ f h₂ g₁ h₂' g₂ :=
    ⟨hwL, hw₂L, hw₂w.symm, hw3, fun g => by rw [hw₂3]; tauto,
      n1, n2, n3, k3, k1.symm, k2.symm, hx₂ f h₂ cf n2 ch₂, hx₂ f h₂' cf n2 ch₂',
      hx₂ g₁ h₂ cg₁ n3 ch₂, hx₂ g₁ h₂' cg₁ n3 ch₂'⟩
  have hmem : ∀ (s t x : W), x ∈ ({s, t} : Finset W) ↔ x = s ∨ x = t := by
    intro s t x; simp only [Finset.mem_insert, Finset.mem_singleton]
  have hout : ∀ t : W, v ≠ t → epOut α β {w, t} f = v := by
    intro t hvt
    unfold epOut
    rcases hfends with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · rw [if_neg (by rw [a1, hmem]; exact fun h' => h'.elim (fun h'' => hwv h''.symm) hvt)]
      exact a1
    · rw [if_pos (by rw [a1, hmem]; exact Or.inl rfl)]
      exact a2
  refine ⟨w, w₁, w₂, f, g₁, g₂, h₁, h₁', h₂, h₂', hP1, hP2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hu, ← hv, hmem, hmem]
    exact fun h' => h'.elim (fun h'' => h''.elim huw huw₁)
      (fun h'' => h''.elim (fun h3 => hwv h3.symm) hvw₁)
  · rw [← hu, ← hv, hmem, hmem]
    exact fun h' => h'.elim (fun h'' => h''.elim huw huw₂)
      (fun h'' => h''.elim (fun h3 => hwv h3.symm) hvw₂)
  · rw [hout w₁ hvw₁]; exact (hecr v).mpr (Or.inr rfl)
  · rw [hout w₂ hvw₂]; exact (hecr v).mpr (Or.inr rfl)
  · intro M hM heM
    -- `f ∉ M`
    have hfM : f ∉ M := by
      intro hfM
      obtain ⟨g₀, -, huniq⟩ := hM.2 v hbL
      exact hfe ((huniq f ⟨hfM, (hfcr v).mpr (Or.inl rfl)⟩).trans
        (huniq e ⟨heM, (hecr v).mpr (Or.inr rfl)⟩).symm)
    obtain ⟨g₀, ⟨hg₀M, hg₀c⟩, huniq⟩ := hM.2 w hwL
    rcases (hw3 g₀).mp hg₀c with rfl | rfl | rfl
    · exact absurd hg₀M hfM
    · -- `g₁ ∈ M`: then `w₂` is covered by `h₂` or `h₂'`
      have hg₂M : g₂ ∉ M := fun h' => n3 (huniq g₂ ⟨h', cg₂⟩).symm
      obtain ⟨g', ⟨hg'M, hg'c⟩, -⟩ := hM.2 w₂ hw₂L
      rcases (hw₂3 g').mp hg'c with rfl | rfl | rfl
      · exact absurd hg'M hg₂M
      · exact Or.inr (Or.inr (Or.inl hg'M))
      · exact Or.inr (Or.inr (Or.inr hg'M))
    · have hg₁M : g₁ ∉ M := fun h' => n3 (huniq g₁ ⟨h', cg₁⟩)
      obtain ⟨g', ⟨hg'M, hg'c⟩, -⟩ := hM.2 w₁ hw₁L
      rcases (hw₁3 g').mp hg'c with rfl | rfl | rfl
      · exact absurd hg'M hg₁M
      · exact Or.inl hg'M
      · exact Or.inr (Or.inl hg'M)

open Classical in
lemma ep_count_four {E : Type*} (S : Finset (Finset E)) (b₁ b₂ b₃ b₄ : E)
    (hcov : ∀ M ∈ S, b₁ ∈ M ∨ b₂ ∈ M ∨ b₃ ∈ M ∨ b₄ ∈ M) :
    (S.filter (fun M => b₁ ∉ M)).card + (S.filter (fun M => b₂ ∉ M)).card +
      (S.filter (fun M => b₃ ∉ M)).card + (S.filter (fun M => b₄ ∉ M)).card ≤ 3 * S.card := by
  simp only [Finset.card_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  calc _ ≤ ∑ _M ∈ S, 3 := Finset.sum_le_sum (fun M hM => by
        rcases hcov M hM with h' | h' | h' | h' <;> simp only [h', not_true_eq_false, if_false] <;>
          split_ifs <;> omega)
    _ = 3 * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

set_option maxHeartbeats 1600000 in
open Classical in
/-- **Lemma 13, Case 1.** The statement of Lemma 13 for a cyclically 4-edge-connected
multigraph with at least six vertices, assuming it for all smaller multigraphs. -/
theorem ep_l13_cyc4 {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (h : EpCubicD α β L) (h4 : EpCyc4 α β L) (h6 : 6 ≤ L.card)
    (IH : ∀ (α₁ β₁ : E → W) (L₁ : Finset W), L₁.card < L.card → EpCubicD α₁ β₁ L₁ →
      EpBridgeless α₁ β₁ L₁ → EpConnected α₁ β₁ L₁ → EpPruned α₁ β₁ L₁ → EpHasCore α₁ β₁ L₁ →
      EpL13 α₁ β₁ L₁) : EpL13 α β L := by
  intro F hF e heL
  have hF0 := ep_fw_bound_nonneg α β L F hF
  have htwo : 2 ≤ epMe α β L e := by
    obtain ⟨M₁, M₂, hM₁, hM₂, hne, h1, h2⟩ := epD_lemma22 α β L h h4 h6 e heL
    unfold epMe
    have : ({M₁, M₂} : Finset (Finset E)) ⊆ (epPMs α β L).filter (fun M => e ∈ M) := by
      intro M hM
      rcases Finset.mem_insert.mp hM with rfl | hM
      · exact Finset.mem_filter.mpr ⟨(mem_epPMs _ _ _ _).mpr hM₁, h1⟩
      · rw [Finset.mem_singleton.mp hM]
        exact Finset.mem_filter.mpr ⟨(mem_epPMs _ _ _ _).mpr hM₂, h2⟩
    have := Finset.card_le_card this
    rw [Finset.card_pair hne] at this
    exact this
  by_cases hsmall : L.card ≤ 599
  · refine ep_l13_of_two α β L F e ?_ htwo
    have : (L.card : ℝ) ≤ 599 := by exact_mod_cast hsmall
    linarith
  · push_neg at hsmall
    obtain ⟨w, w₁, w₂, f, g₁, g₂, h₁, h₁', h₂, h₂', hP1, hP2, het₁, het₂, hcr₁, hcr₂, hcov⟩ :=
      ep_cyc4_local α β L h h4 h6 e heL
    have hnotri := ep_cyc4_no_triangle α β L h h4 h6
    have hlive : ∀ g, α g ≠ β g → α g ∈ L ∧ β g ∈ L := by
      intro g hg
      rcases h.1 g with h' | h'
      · exact ⟨h'.1, h'.2.1⟩
      · exact absurd h'.2.symm hg
    obtain ⟨a1, a2⟩ := hP1.outer_ne hlive hnotri
    obtain ⟨a3, a4⟩ := hP1.swap.outer_ne hlive hnotri
    obtain ⟨a5, a6⟩ := hP2.outer_ne hlive hnotri
    obtain ⟨a7, a8⟩ := hP2.swap.outer_ne hlive hnotri
    have heavy : (∃ 𝒳, EpFol0 α β L 𝒳 ∧
        ((L.card : ℝ) - 6) / 995 + 98 / 995 - 2 * (196 / 995) ≤ epFw α β 𝒳) →
        (2 : ℝ) ^ ((L.card : ℝ) / 995 - F + 396 / 995) ≤ (epMe α β L e : ℝ) := by
      rintro ⟨𝒳, hfol, hw⟩
      refine ep_l13_of_two α β L F e ?_ htwo
      have := hF 𝒳 hfol
      linarith
    rcases ep_split_package α β L w w₁ f h₁ g₂ h₁' g₁ h h4 (by omega) hP1 a1 a2 e heL het₁ hcr₁ IH
      with hh | B1
    · exact heavy hh
    rcases ep_split_package α β L w w₁ f h₁' g₂ h₁ g₁ h h4 (by omega) hP1.swap a3 a4 e heL het₁
      hcr₁ IH with hh | B2
    · exact heavy hh
    rcases ep_split_package α β L w w₂ f h₂ g₁ h₂' g₂ h h4 (by omega) hP2 a5 a6 e heL het₂ hcr₂ IH
      with hh | B3
    · exact heavy hh
    rcases ep_split_package α β L w w₂ f h₂' g₁ h₂ g₂ h h4 (by omega) hP2.swap a7 a8 e heL het₂
      hcr₂ IH with hh | B4
    · exact heavy hh
    have b1 := B1 F hF
    have b2 := B2 F hF
    have b3 := B3 F hF
    have b4 := B4 F hF
    have hcount := ep_count_four ((epPMs α β L).filter (fun M => e ∈ M)) h₁ h₁' h₂ h₂'
      (fun M hM => hcov M ((mem_epPMs _ _ _ _).mp (Finset.mem_filter.mp hM).1)
        (Finset.mem_filter.mp hM).2)
    simp only [Finset.filter_filter] at hcount
    have hcount' : ((((epPMs α β L).filter (fun M => e ∈ M ∧ h₁ ∉ M)).card : ℝ) +
        (((epPMs α β L).filter (fun M => e ∈ M ∧ h₁' ∉ M)).card : ℝ) +
        (((epPMs α β L).filter (fun M => e ∈ M ∧ h₂ ∉ M)).card : ℝ) +
        (((epPMs α β L).filter (fun M => e ∈ M ∧ h₂' ∉ M)).card : ℝ)) ≤
        3 * (epMe α β L e : ℝ) := by
      unfold epMe
      exact_mod_cast hcount
    have hsplit : (2 : ℝ) ^ ((L.card : ℝ) / 995 - F + 396 / 995) =
        (2 : ℝ) ^ (((L.card : ℝ) - 6) / 995 - (F + 2 * (196 / 995)) + 396 / 995) *
          (2 : ℝ) ^ ((2 : ℝ) / 5) := by
      rw [← Real.rpow_add (by norm_num)]
      congr 1
      ring
    rw [hsplit]
    have hpos : (0 : ℝ) ≤
        (2 : ℝ) ^ (((L.card : ℝ) - 6) / 995 - (F + 2 * (196 / 995)) + 396 / 995) :=
      Real.rpow_nonneg (by norm_num) _
    have h9 := lp_const9
    nlinarith [mul_le_mul_of_nonneg_left h9 hpos]

open Classical in
/-- A **core partition**: a partition of `L` into `n ≥ 6` nonempty blobs, each with a cut of
size three, whose quotient is cyclically 4-edge-connected: the union of a nonempty proper set
of blobs has a cut of size at least three, and exactly three only for one blob or all but one. -/
def EpCorePart {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (n : ℕ)
    (Z : Fin n → Finset W) : Prop :=
  6 ≤ n ∧ (∀ i, (Z i).Nonempty ∧ Z i ⊆ L ∧ (epCut α β (Z i)).card = 3) ∧
    (∀ i j, i ≠ j → Disjoint (Z i) (Z j)) ∧ (∀ w ∈ L, ∃ i, w ∈ Z i) ∧
    ∀ I : Finset (Fin n), I.Nonempty → I ≠ Finset.univ →
      3 ≤ (epCut α β (I.biUnion Z)).card ∧
        ((epCut α β (I.biUnion Z)).card = 3 → I.card = 1 ∨ Iᶜ.card = 1)

open Classical in
/-- Lifting commutes with unions of blobs. -/
lemma ep_lift_biUnion {W : Type*} {n : ℕ} (μ : W) (X : Finset W) (Z : Fin n → Finset W)
    (I : Finset (Fin n)) :
    I.biUnion (fun i => if μ ∈ Z i then Z i ∪ X else Z i) =
      (if μ ∈ I.biUnion Z then I.biUnion Z ∪ X else I.biUnion Z) := by
  ext w
  by_cases hμ : μ ∈ I.biUnion Z
  · rw [if_pos hμ, Finset.mem_union]
    simp only [Finset.mem_biUnion]
    constructor
    · rintro ⟨i, hi, hw⟩
      by_cases hμi : μ ∈ Z i
      · rw [if_pos hμi, Finset.mem_union] at hw
        exact hw.elim (fun h' => Or.inl ⟨i, hi, h'⟩) Or.inr
      · rw [if_neg hμi] at hw; exact Or.inl ⟨i, hi, hw⟩
    · rintro (⟨i, hi, hw⟩ | hw)
      · refine ⟨i, hi, ?_⟩
        by_cases hμi : μ ∈ Z i
        · rw [if_pos hμi]; exact Finset.mem_union_left _ hw
        · rw [if_neg hμi]; exact hw
      · obtain ⟨i, hi, hμi⟩ := Finset.mem_biUnion.mp hμ
        exact ⟨i, hi, by rw [if_pos hμi]; exact Finset.mem_union_right _ hw⟩
  · rw [if_neg hμ]
    simp only [Finset.mem_biUnion]
    constructor
    · rintro ⟨i, hi, hw⟩
      have hμi : μ ∉ Z i := fun h' => hμ (Finset.mem_biUnion.mpr ⟨i, hi, h'⟩)
      rw [if_neg hμi] at hw
      exact ⟨i, hi, hw⟩
    · rintro ⟨i, hi, hw⟩
      have hμi : μ ∉ Z i := fun h' => hμ (Finset.mem_biUnion.mpr ⟨i, hi, h'⟩)
      exact ⟨i, hi, by rw [if_neg hμi]; exact hw⟩

set_option maxHeartbeats 800000 in
open Classical in
/-- A core partition of a contraction lifts to a core partition of the multigraph. -/
theorem ep_corePart_lift {W E : Type*} [Fintype E] (α β α₁ β₁ : E → W) (L L₁ X : Finset W)
    (μ : W) (hμ : μ ∈ L₁) (hL : ∀ w, w ∈ L ↔ w ∈ L₁ ∨ w ∈ X)
    (hdisj : ∀ w, w ∈ L₁ → w ≠ μ → w ∉ X)
    (hcut : ∀ T', T' ⊆ L₁ →
      (epCut α₁ β₁ T').card = (epCut α β (if μ ∈ T' then T' ∪ X else T')).card)
    (n : ℕ) (Z : Fin n → Finset W) (hZ : EpCorePart α₁ β₁ L₁ n Z) :
    EpCorePart α β L n (fun i => if μ ∈ Z i then Z i ∪ X else Z i) := by
  obtain ⟨h6, hblob, hdis, hcov, hun⟩ := hZ
  have hsub : ∀ I : Finset (Fin n), I.biUnion Z ⊆ L₁ := by
    intro I w hw
    obtain ⟨i, -, hwi⟩ := Finset.mem_biUnion.mp hw
    exact (hblob i).2.1 hwi
  have hmemlift : ∀ i w, w ∈ (if μ ∈ Z i then Z i ∪ X else Z i) ↔ w ∈ Z i ∨ (μ ∈ Z i ∧ w ∈ X) := by
    intro i w
    by_cases hμi : μ ∈ Z i
    · rw [if_pos hμi, Finset.mem_union]
      exact ⟨fun h' => h'.elim Or.inl (fun h'' => Or.inr ⟨hμi, h''⟩),
        fun h' => h'.elim Or.inl (fun h'' => Or.inr h''.2)⟩
    · rw [if_neg hμi]
      exact ⟨Or.inl, fun h' => h'.elim id (fun h'' => absurd h''.1 hμi)⟩
  refine ⟨h6, fun i => ⟨?_, ?_, ?_⟩, fun i j hij => ?_, fun w hw => ?_, fun I hI hIu => ?_⟩
  · obtain ⟨w, hw⟩ := (hblob i).1
    exact ⟨w, (hmemlift i w).mpr (Or.inl hw)⟩
  · intro w hw
    rcases (hmemlift i w).mp hw with h' | h'
    · exact (hL w).mpr (Or.inl ((hblob i).2.1 h'))
    · exact (hL w).mpr (Or.inr h'.2)
  · rw [← hcut (Z i) (hblob i).2.1]; exact (hblob i).2.2
  · rw [Finset.disjoint_left]
    intro w hw hw'
    have hd := Finset.disjoint_left.mp (hdis i j hij)
    rcases (hmemlift i w).mp hw with a | a <;> rcases (hmemlift j w).mp hw' with b | b
    · exact hd a b
    · by_cases hwμ : w = μ
      · exact hd (hwμ ▸ a) b.1
      · exact hdisj w ((hblob i).2.1 a) hwμ b.2
    · by_cases hwμ : w = μ
      · exact hd a.1 (hwμ ▸ b)
      · exact hdisj w ((hblob j).2.1 b) hwμ a.2
    · exact hd a.1 b.1
  · rcases (hL w).mp hw with h' | h'
    · obtain ⟨i, hi⟩ := hcov w h'
      exact ⟨i, (hmemlift i w).mpr (Or.inl hi)⟩
    · obtain ⟨i, hi⟩ := hcov μ hμ
      exact ⟨i, (hmemlift i w).mpr (Or.inr ⟨hi, h'⟩)⟩
  · rw [ep_lift_biUnion μ X Z I, ← hcut _ (hsub I)]
    exact hun I hI hIu

set_option maxHeartbeats 800000 in
open Classical in
/-- If the lifts of a family of sets form a core partition of the multigraph, the family is a
core partition of the contraction. -/
theorem ep_corePart_unlift {W E : Type*} [Fintype E] (α β α₁ β₁ : E → W) (L L₁ X : Finset W)
    (μ : W) (hL₁ : L₁ ⊆ L) (hdisj : ∀ w, w ∈ L₁ → w ≠ μ → w ∉ X)
    (hcut : ∀ T', T' ⊆ L₁ →
      (epCut α₁ β₁ T').card = (epCut α β (if μ ∈ T' then T' ∪ X else T')).card)
    (n : ℕ) (Z' : Fin n → Finset W) (hZ'1 : ∀ i, (Z' i).Nonempty ∧ Z' i ⊆ L₁)
    (hZ : EpCorePart α β L n (fun i => if μ ∈ Z' i then Z' i ∪ X else Z' i)) :
    EpCorePart α₁ β₁ L₁ n Z' := by
  obtain ⟨h6, hblob, hdis, hcov, hun⟩ := hZ
  have hsub : ∀ I : Finset (Fin n), I.biUnion Z' ⊆ L₁ := by
    intro I w hw
    obtain ⟨i, -, hwi⟩ := Finset.mem_biUnion.mp hw
    exact (hZ'1 i).2 hwi
  have hsublift : ∀ i, Z' i ⊆ (if μ ∈ Z' i then Z' i ∪ X else Z' i) := by
    intro i
    by_cases hμi : μ ∈ Z' i
    · rw [if_pos hμi]; exact Finset.subset_union_left
    · rw [if_neg hμi]
  refine ⟨h6, fun i => ⟨(hZ'1 i).1, (hZ'1 i).2, ?_⟩, fun i j hij => ?_, fun w hw => ?_,
    fun I hI hIu => ?_⟩
  · rw [hcut (Z' i) (hZ'1 i).2]; exact (hblob i).2.2
  · exact Finset.disjoint_of_subset_left (hsublift i)
      (Finset.disjoint_of_subset_right (hsublift j) (hdis i j hij))
  · obtain ⟨i, hi⟩ := hcov w (hL₁ hw)
    have hi : w ∈ (if μ ∈ Z' i then Z' i ∪ X else Z' i) := hi
    by_cases hμi : μ ∈ Z' i
    · rw [if_pos hμi, Finset.mem_union] at hi
      rcases hi with h' | h'
      · exact ⟨i, h'⟩
      · by_cases hwμ : w = μ
        · exact ⟨i, hwμ ▸ hμi⟩
        · exact absurd h' (hdisj w hw hwμ)
    · rw [if_neg hμi] at hi; exact ⟨i, hi⟩
  · have := hun I hI hIu
    rw [ep_lift_biUnion μ X Z' I, ← hcut _ (hsub I)] at this
    exact this

open Classical in
lemma ep_corePart_card {W : Type*} {n : ℕ} (Z : Fin n → Finset W)
    (hdis : ∀ i j, i ≠ j → Disjoint (Z i) (Z j)) (I : Finset (Fin n))
    (h1 : ∀ i ∈ I, (Z i).card = 1) : (I.biUnion Z).card = I.card := by
  rw [Finset.card_biUnion (fun i _ j _ hij => hdis i j hij), Finset.sum_congr rfl h1]
  simp

set_option maxHeartbeats 800000 in
open Classical in
/-- A cyclically 4-edge-connected multigraph with at least six vertices has the core partition
into singletons. -/
theorem ep_corePart_of_cyc4 {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (h : EpCubicD α β L) (h4 : EpCyc4 α β L) (h6 : 6 ≤ L.card) :
    ∃ Z : Fin L.card → Finset W, EpCorePart α β L L.card Z := by
  obtain ⟨f, hf⟩ : ∃ f : Fin L.card → W, ∀ i, f i = (L.equivFin.symm i).val := ⟨_, fun _ => rfl⟩
  have hfL : ∀ i, f i ∈ L := fun i => by rw [hf]; exact (L.equivFin.symm i).2
  have hfinj : ∀ i j, f i = f j → i = j := by
    intro i j hij
    rw [hf, hf] at hij
    exact L.equivFin.symm.injective (Subtype.ext hij)
  have hfsurj : ∀ w ∈ L, ∃ i, f i = w := by
    intro w hw
    exact ⟨L.equivFin ⟨w, hw⟩, by rw [hf, Equiv.symm_apply_apply]⟩
  have hdis : ∀ i j : Fin L.card, i ≠ j → Disjoint ({f i} : Finset W) {f j} := fun i j hij =>
    Finset.disjoint_singleton.mpr (fun h' => hij (hfinj i j h'))
  refine ⟨fun i => {f i}, h6, fun i => ⟨Finset.singleton_nonempty _,
    Finset.singleton_subset_iff.mpr (hfL i), h.2 _ (hfL i)⟩, hdis, fun w hw => ?_,
    fun I hI hIu => ?_⟩
  · obtain ⟨i, hi⟩ := hfsurj w hw
    exact ⟨i, by show w ∈ ({f i} : Finset W); rw [hi]; exact Finset.mem_singleton_self w⟩
  · have hTL : I.biUnion (fun i => ({f i} : Finset W)) ⊆ L := by
      intro w hw
      obtain ⟨i, -, hwi⟩ := Finset.mem_biUnion.mp hw
      rw [Finset.mem_singleton.mp hwi]; exact hfL i
    have hTne : (I.biUnion (fun i => ({f i} : Finset W))).Nonempty := by
      obtain ⟨i, hi⟩ := hI
      exact ⟨f i, Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_singleton_self _⟩⟩
    obtain ⟨j, hj⟩ : ∃ j, j ∉ I := by
      by_contra hcon
      push_neg at hcon
      exact hIu (Finset.eq_univ_iff_forall.mpr hcon)
    have hTneL : I.biUnion (fun i => ({f i} : Finset W)) ≠ L := by
      intro h'
      have : f j ∈ I.biUnion (fun i => ({f i} : Finset W)) := by rw [h']; exact hfL j
      obtain ⟨i, hi, hji⟩ := Finset.mem_biUnion.mp this
      exact hj ((hfinj j i (Finset.mem_singleton.mp hji)) ▸ hi)
    refine ⟨h4.1 _ hTL hTne hTneL, fun h3 => ?_⟩
    have hc := ep_corePart_card (fun i => ({f i} : Finset W)) hdis I
      (fun i _ => Finset.card_singleton _)
    have hsd := Finset.card_sdiff_add_card_eq_card hTL
    have hcompl : Iᶜ.card = L.card - I.card := by
      rw [Finset.card_compl, Fintype.card_fin]
    have hle := Finset.card_le_card hTL
    rcases h4.2 _ hTL h3 with h' | h'
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

set_option maxHeartbeats 800000 in
open Classical in
/-- A core partition into singletons means that the multigraph is cyclically
4-edge-connected with `n` vertices. -/
theorem ep_cyc4_of_corePart {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (h : EpCubicD α β L) (n : ℕ) (Z : Fin n → Finset W) (hZ : EpCorePart α β L n Z)
    (h1 : ∀ i, (Z i).card = 1) : EpCyc4 α β L ∧ L.card = n := by
  obtain ⟨h6, hblob, hdis, hcov, hun⟩ := hZ
  have hrep : ∀ T : Finset W, T ⊆ L →
      T = (Finset.univ.filter (fun i => Z i ⊆ T)).biUnion Z ∧
      L \ T = (Finset.univ.filter (fun i => Z i ⊆ T))ᶜ.biUnion Z := by
    intro T hT
    have hsing : ∀ i w, w ∈ Z i → Z i = {w} := by
      intro i w hw
      obtain ⟨v, hv⟩ := Finset.card_eq_one.mp (h1 i)
      rw [hv] at hw ⊢
      rw [Finset.mem_singleton.mp hw]
    constructor
    · ext w
      rw [Finset.mem_biUnion]
      constructor
      · intro hw
        obtain ⟨i, hi⟩ := hcov w (hT hw)
        exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          rw [hsing i w hi]; exact Finset.singleton_subset_iff.mpr hw⟩, hi⟩
      · rintro ⟨i, hi, hw⟩
        exact (Finset.mem_filter.mp hi).2 hw
    · ext w
      rw [Finset.mem_sdiff, Finset.mem_biUnion]
      constructor
      · rintro ⟨hwL, hwT⟩
        obtain ⟨i, hi⟩ := hcov w hwL
        refine ⟨i, ?_, hi⟩
        rw [Finset.mem_compl, Finset.mem_filter]
        exact fun h' => hwT (h'.2 hi)
      · rintro ⟨i, hi, hw⟩
        rw [Finset.mem_compl, Finset.mem_filter] at hi
        refine ⟨(hblob i).2.1 hw, fun hwT => hi ⟨Finset.mem_univ _, ?_⟩⟩
        rw [hsing i w hw]; exact Finset.singleton_subset_iff.mpr hwT
  have hLn : L.card = n := by
    have := (hrep L (Finset.Subset.refl _)).1
    have hall : Finset.univ.filter (fun i => Z i ⊆ L) = Finset.univ :=
      Finset.filter_true_of_mem (fun i _ => (hblob i).2.1)
    rw [hall] at this
    rw [this, ep_corePart_card Z hdis _ (fun i _ => h1 i), Finset.card_univ, Fintype.card_fin]
  have hI : ∀ T : Finset W, T ⊆ L → T.Nonempty → T ≠ L →
      (Finset.univ.filter (fun i => Z i ⊆ T)).Nonempty ∧
        Finset.univ.filter (fun i => Z i ⊆ T) ≠ Finset.univ := by
    intro T hT hne hneL
    obtain ⟨e1, e2⟩ := hrep T hT
    constructor
    · by_contra hcon
      rw [Finset.not_nonempty_iff_eq_empty] at hcon
      rw [hcon, Finset.biUnion_empty] at e1
      exact hne.ne_empty e1
    · intro hcon
      apply hneL
      rw [hcon, Finset.compl_univ, Finset.biUnion_empty, Finset.sdiff_eq_empty_iff_subset] at e2
      exact Finset.Subset.antisymm hT e2
  refine ⟨⟨fun T hT hne hneL => ?_, fun T hT h3 => ?_⟩, hLn⟩
  · obtain ⟨a1, a2⟩ := hI T hT hne hneL
    have := (hun _ a1 a2).1
    rw [← (hrep T hT).1] at this
    exact this
  · have hne : T.Nonempty := by
      by_contra hcon
      rw [Finset.not_nonempty_iff_eq_empty] at hcon
      have : epCut α β T = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro g hg
        rw [mem_epCut, hcon] at hg
        unfold epCross at hg
        simp at hg
      rw [this, Finset.card_empty] at h3
      omega
    have hneL : T ≠ L := by
      intro hcon
      have : epCut α β T = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro g hg
        rw [mem_epCut, hcon] at hg
        unfold epCross at hg
        rcases h.1 g with ⟨l1, l2, -⟩ | ⟨l1, l2⟩
        · exact hg.elim (fun h' => h'.2 l2) (fun h' => h'.1 l1)
        · rw [l2] at hg; exact hg.elim (fun h' => h'.2 h'.1) (fun h' => h'.1 h'.2)
      rw [this, Finset.card_empty] at h3
      omega
    obtain ⟨a1, a2⟩ := hI T hT hne hneL
    obtain ⟨e1, e2⟩ := hrep T hT
    have h3' : (epCut α β ((Finset.univ.filter (fun i => Z i ⊆ T)).biUnion Z)).card = 3 := by
      rw [← e1]; exact h3
    have c1 := ep_corePart_card Z hdis (Finset.univ.filter (fun i => Z i ⊆ T)) (fun i _ => h1 i)
    have c2 := ep_corePart_card Z hdis (Finset.univ.filter (fun i => Z i ⊆ T))ᶜ (fun i _ => h1 i)
    rw [← e1] at c1
    rw [← e2] at c2
    rcases (hun _ a1 a2).2 h3' with h' | h'
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

set_option maxHeartbeats 800000 in
open Classical in
/-- **Contraction inside a blob.** Contracting a set `X` inside the blob `Z i₀` gives a core
partition of the contraction, in which the blob becomes `insert x₀ (Z i₀ \ X)`. -/
theorem ep_corePart_contract {W E : Type*} [Fintype E] (α β : E → W) (L X : Finset W)
    (x₀ x₁ : W) (n : ℕ) (Z : Fin n → Finset W) (hZ : EpCorePart α β L n Z) (i₀ : Fin n)
    (hX : X ⊆ Z i₀) (hx₀ : x₀ ∈ X) :
    EpCorePart (epConA α β X x₀ x₁) (epConB α β X x₀ x₁) (epL' L X x₀) n
      (fun i => if i = i₀ then insert x₀ (Z i₀ \ X) else Z i) := by
  have hblob := hZ.2.1
  have hdis := hZ.2.2.1
  have hXL : X ⊆ L := hX.trans (hblob i₀).2.1
  have hx₀i : ∀ i, i ≠ i₀ → x₀ ∉ Z i := fun i hi h' =>
    Finset.disjoint_left.mp (hdis i i₀ hi) h' (hX hx₀)
  have hlift : (fun i => if x₀ ∈ (if i = i₀ then insert x₀ (Z i₀ \ X) else Z i) then
      (if i = i₀ then insert x₀ (Z i₀ \ X) else Z i) ∪ X else
      (if i = i₀ then insert x₀ (Z i₀ \ X) else Z i)) = Z := by
    funext i
    by_cases hi : i = i₀
    · rw [if_pos hi, if_pos (Finset.mem_insert_self _ _), hi]
      ext w
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_sdiff]
      constructor
      · rintro ((rfl | h') | h')
        · exact hX hx₀
        · exact h'.1
        · exact hX h'
      · intro hw
        by_cases hwX : w ∈ X
        · exact Or.inr hwX
        · exact Or.inl (Or.inr ⟨hw, hwX⟩)
    · rw [if_neg hi, if_neg (hx₀i i hi)]
  refine ep_corePart_unlift α β _ _ L (epL' L X x₀) X x₀ ?_ ?_ ?_ n _ ?_ (by rw [hlift]; exact hZ)
  · intro w hw
    unfold epL' at hw
    rcases Finset.mem_insert.mp hw with rfl | h'
    · exact hXL hx₀
    · exact (Finset.mem_sdiff.mp h').1
  · intro w hw hwx
    unfold epL' at hw
    rcases Finset.mem_insert.mp hw with h' | h'
    · exact absurd h' hwx
    · exact (Finset.mem_sdiff.mp h').2
  · intro T' hT'
    rw [epCon_cut α β L X x₀ x₁ hx₀ T' hT']
    rfl
  · intro i
    by_cases hi : i = i₀
    · rw [if_pos hi]
      refine ⟨⟨x₀, Finset.mem_insert_self _ _⟩, fun w hw => ?_⟩
      unfold epL'
      rcases Finset.mem_insert.mp hw with rfl | h'
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr
          ⟨(hblob i₀).2.1 (Finset.mem_sdiff.mp h').1, (Finset.mem_sdiff.mp h').2⟩)
    · rw [if_neg hi]
      refine ⟨(hblob i).1, fun w hw => ?_⟩
      unfold epL'
      exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨(hblob i).2.1 hw,
        fun h' => Finset.disjoint_left.mp (hdis i i₀ hi) hw (hX h')⟩)

set_option maxHeartbeats 800000 in
open Classical in
/-- **A core partition gives a core.** -/
theorem ep_core_of_corePart {W E : Type*} [Fintype E] : ∀ (m : ℕ) (α β : E → W) (L : Finset W)
    (n : ℕ) (Z : Fin n → Finset W), L.card = m → EpCubicD α β L → EpBridgeless α β L →
    EpConnected α β L → EpCorePart α β L n Z → EpHasCore α β L := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro α β L n Z hm h hb hconn hZ
    by_cases hall : ∀ i, (Z i).card = 1
    · obtain ⟨h4, hLn⟩ := ep_cyc4_of_corePart α β L h n Z hZ hall
      exact ⟨α, β, L, Relation.ReflTransGen.refl, h4, by rw [hLn]; exact hZ.1⟩
    · push_neg at hall
      obtain ⟨i₀, hi₀⟩ := hall
      obtain ⟨hne, hsub, hcut⟩ := hZ.2.1 i₀
      obtain ⟨x₀, hx₀, x₁, hx₁, hx⟩ := Finset.one_lt_card.mp (by
        have := Finset.card_pos.mpr hne; omega : 1 < (Z i₀).card)
      have hstep : EpStep α β L (epConA α β (Z i₀) x₀ x₁) (epConB α β (Z i₀) x₀ x₁)
          (epL' L (Z i₀) x₀) :=
        Or.inl ⟨Z i₀, x₀, x₁, hsub, hx₀, hx₁, hx.symm, hcut, rfl, rfl, rfl⟩
      obtain ⟨h₁, hb₁, hconn₁, -, hlt⟩ := hstep.preserves h hb hconn
      have hZ₁ := ep_corePart_contract α β L (Z i₀) x₀ x₁ n Z hZ i₀ (Finset.Subset.refl _) hx₀
      exact EpHasCore.of_step hstep
        (ih _ (by omega) _ _ _ n _ rfl h₁ hb₁ hconn₁ hZ₁)

set_option maxHeartbeats 800000 in
open Classical in
/-- A core partition of the result of a cut-contraction step lifts to the multigraph. -/
lemma ep_corePart_step {W E : Type*} [Fintype E] (α₀ β₀ : E → W) (L₀ : Finset W)
    (α₁ β₁ : E → W) (L₁ : Finset W) (hstep : EpStep α₀ β₀ L₀ α₁ β₁ L₁)
    (ha : EpCubicD α₀ β₀ L₀) (hba : EpBridgeless α₀ β₀ L₀)
    (hc : ∃ (n : ℕ) (Z : Fin n → Finset W), EpCorePart α₁ β₁ L₁ n Z) :
    ∃ (n : ℕ) (Z : Fin n → Finset W), EpCorePart α₀ β₀ L₀ n Z := by
  obtain ⟨n, Z, hZ⟩ := hc
  rcases hstep with ⟨X, x₀, x₁, hXL, hx₀, hx₁, hne, h3, rfl, rfl, rfl⟩ |
    ⟨X, e, e', x₁, hXL, hx₁, hee', hcut, rfl, rfl, rfl⟩
  · refine ⟨n, _, ep_corePart_lift α₀ β₀ _ _ L₀ _ X x₀ ?_ ?_ ?_ ?_ n Z hZ⟩
    · unfold epL'; exact Finset.mem_insert_self _ _
    · intro w
      unfold epL'
      rw [Finset.mem_insert, Finset.mem_sdiff]
      constructor
      · intro hw
        by_cases hwX : w ∈ X
        · exact Or.inr hwX
        · exact Or.inl (Or.inr ⟨hw, hwX⟩)
      · rintro ((rfl | h') | h')
        · exact hXL hx₀
        · exact h'.1
        · exact hXL h'
    · intro w hw hwx
      unfold epL' at hw
      rcases Finset.mem_insert.mp hw with h' | h'
      · exact absurd h' hwx
      · exact (Finset.mem_sdiff.mp h').2
    · intro T' hT'
      rw [epCon_cut α₀ β₀ L₀ X x₀ x₁ hx₀ T' hT']
      rfl
  · obtain ⟨a1, a2, -, -⟩ := ep_cut_insert_card α₀ β₀ L₀ X ha hba hXL e e' hee' hcut e'
      (Or.inr rfl)
    refine ⟨n, _, ep_corePart_lift α₀ β₀ _ _ L₀ _ X (epOut α₀ β₀ X e') ?_ ?_ ?_ ?_ n Z hZ⟩
    · exact Finset.mem_sdiff.mpr ⟨a1, a2⟩
    · intro w
      rw [Finset.mem_sdiff]
      constructor
      · intro hw
        by_cases hwX : w ∈ X
        · exact Or.inr hwX
        · exact Or.inl ⟨hw, hwX⟩
      · rintro (h' | h')
        · exact h'.1
        · exact hXL h'
    · intro w hw _
      exact (Finset.mem_sdiff.mp hw).2
    · intro T' hT'
      rw [ep2_cut α₀ β₀ X e e' x₁ hcut T' (fun w hw => (Finset.mem_sdiff.mp (hT' hw)).2)]
      rfl

open Classical in
/-- **A core gives a core partition.** -/
theorem ep_corePart_of_core {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (h : EpCubicD α β L) (hb : EpBridgeless α β L) (hconn : EpConnected α β L)
    (hc : EpHasCore α β L) : ∃ (n : ℕ) (Z : Fin n → Finset W), EpCorePart α β L n Z := by
  obtain ⟨α', β', L', hreach, h4, h6⟩ := hc
  unfold EpReach at hreach
  have key : ∀ a : (E → W) × (E → W) × Finset W,
      Relation.ReflTransGen
        (fun a b : (E → W) × (E → W) × Finset W => EpStep a.1 a.2.1 a.2.2 b.1 b.2.1 b.2.2)
        a (α', β', L') →
      EpCubicD a.1 a.2.1 a.2.2 → EpBridgeless a.1 a.2.1 a.2.2 → EpConnected a.1 a.2.1 a.2.2 →
      ∃ (n : ℕ) (Z : Fin n → Finset W), EpCorePart a.1 a.2.1 a.2.2 n Z := by
    intro a ha
    induction ha using Relation.ReflTransGen.head_induction_on with
    | refl =>
      intro h' _ _
      exact ⟨L'.card, ep_corePart_of_cyc4 α' β' L' h' h4 h6⟩
    | head hstep _ ih =>
      intro ha hba hca
      obtain ⟨h₁, hb₁, hconn₁, -, -⟩ := EpStep.preserves hstep ha hba hca
      exact ep_corePart_step _ _ _ _ _ _ hstep ha hba (ih h₁ hb₁ hconn₁)
  exact key (α, β, L) hreach h hb hconn

set_option maxHeartbeats 800000 in
open Classical in
/-- **Triangles lie inside blobs.** -/
theorem ep_corePart_triangle {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (n : ℕ)
    (Z : Fin n → Finset W) (hZ : EpCorePart α β L n Z) (x y z : W) (e1 e2 e3 : E)
    (ht : EpTriangle α β L x y z e1 e2 e3) : ∃ i, x ∈ Z i ∧ y ∈ Z i ∧ z ∈ Z i := by
  obtain ⟨h6, hblob, hdis, hcov, hun⟩ := hZ
  -- an edge joining two vertices in different blobs lies between the blobs
  have hbtw : ∀ (p q : W) (g : E) (i j : Fin n), p ≠ q →
      (∀ w, epCross α β {w} g ↔ w = p ∨ w = q) → p ∈ Z i → q ∈ Z j →
      g ∈ epBtw α β (Z i) (Z j) := by
    intro p q g i j hpq hg hp hq
    have := ep_edge_btw α β p q g hpq hg
    rw [mem_epBtw] at this ⊢
    simp only [Finset.mem_singleton] at this
    rcases this with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · exact Or.inl ⟨a1 ▸ hp, a2 ▸ hq⟩
    · exact Or.inr ⟨a1 ▸ hq, a2 ▸ hp⟩
  have hpair : ∀ i j : Fin n, i ≠ j → (epBtw α β (Z i) (Z j)).card ≤ 1 := by
    intro i j hij
    have e := ep_cut_union α β (Z i) (Z j) (hdis i j hij)
    rw [(hblob i).2.2, (hblob j).2.2] at e
    have hI : ({i, j} : Finset (Fin n)).biUnion Z = Z i ∪ Z j := by
      ext w; simp [Finset.mem_biUnion]
    have hcard : ({i, j} : Finset (Fin n)).card = 2 := Finset.card_pair hij
    have := (hun {i, j} ⟨i, Finset.mem_insert_self _ _⟩ (fun h' => by
      rw [h', Finset.card_univ, Fintype.card_fin] at hcard; omega)).1
    rw [hI] at this
    omega
  -- two vertices of a triangle in one blob force the third into it
  have htwo : ∀ (p q r : W) (f1 f2 f3 : E), EpTriangle α β L p q r f1 f2 f3 →
      ∀ i k, p ∈ Z i → q ∈ Z i → r ∈ Z k → i = k := by
    intro p q r f1 f2 f3 ht' i k hp hq hr
    by_contra hik
    obtain ⟨-, -, -, hpq, hqr, hpr, c1, c2, c3⟩ := ht'
    have b2 := hbtw q r f2 i k hqr c2 hq hr
    have b3 : f3 ∈ epBtw α β (Z i) (Z k) := by
      rw [ep_btw_comm]; exact hbtw r p f3 k i (Ne.symm hpr) c3 hr hp
    have hne : f2 ≠ f3 := by
      intro h'
      have := (c2 q).mpr (Or.inl rfl)
      rw [h', c3] at this
      exact this.elim hqr (fun h'' => hpq h''.symm)
    have : ({f2, f3} : Finset E) ⊆ epBtw α β (Z i) (Z k) := by
      intro g hg
      rcases Finset.mem_insert.mp hg with rfl | hg
      · exact b2
      · rw [Finset.mem_singleton.mp hg]; exact b3
    have := Finset.card_le_card this
    rw [Finset.card_pair hne] at this
    have := hpair i k hik
    omega
  obtain ⟨i, hi⟩ := hcov x ht.1
  obtain ⟨j, hj⟩ := hcov y ht.2.1
  obtain ⟨k, hk⟩ := hcov z ht.2.2.1
  by_cases hij : i = j
  · subst hij
    have := htwo x y z e1 e2 e3 ht i k hi hj hk
    subst this
    exact ⟨i, hi, hj, hk⟩
  · by_cases hjk : j = k
    · subst hjk
      exact absurd (htwo y z x e2 e3 e1 ht.rot j i hj hk hi).symm hij
    · by_cases hik : i = k
      · subst hik
        exact absurd (htwo z x y e3 e1 e2 ht.rot.rot i j hk hi hj) hij
      · -- three different blobs
        exfalso
        obtain ⟨-, -, -, hxy, hyz, hxz, c1, c2, c3⟩ := ht
        have b1 := hbtw x y e1 i j hxy c1 hi hj
        have b2 := hbtw y z e2 j k hyz c2 hj hk
        have b3 : e3 ∈ epBtw α β (Z i) (Z k) := by
          rw [ep_btw_comm]; exact hbtw z x e3 k i (Ne.symm hxz) c3 hk hi
        have u1 := ep_cut_union α β (Z j) (Z k) (hdis j k hjk)
        rw [(hblob j).2.2, (hblob k).2.2] at u1
        have hd : Disjoint (Z i) (Z j ∪ Z k) :=
          Finset.disjoint_union_right.mpr ⟨hdis i j hij, hdis i k hik⟩
        have u2 := ep_cut_union α β (Z i) (Z j ∪ Z k) hd
        rw [(hblob i).2.2] at u2
        have u3 := ep_btw_add α β (Z i) (Z j) (Z k) (hdis i j hij) (hdis i k hik) (hdis j k hjk)
        have p1 := Finset.card_pos.mpr ⟨e1, b1⟩
        have p2 := Finset.card_pos.mpr ⟨e2, b2⟩
        have p3 := Finset.card_pos.mpr ⟨e3, b3⟩
        have hI : ({i, j, k} : Finset (Fin n)).biUnion Z = Z i ∪ (Z j ∪ Z k) := by
          ext w; simp [Finset.mem_biUnion]
        have hcard : ({i, j, k} : Finset (Fin n)).card = 3 :=
          Finset.card_eq_three.mpr ⟨i, j, k, hij, hik, hjk, rfl⟩
        have hne : ({i, j, k} : Finset (Fin n)) ≠ Finset.univ := fun h' => by
          rw [h', Finset.card_univ, Fintype.card_fin] at hcard; omega
        obtain ⟨g1, g2⟩ := hun {i, j, k} ⟨i, Finset.mem_insert_self _ _⟩ hne
        rw [hI] at g1 g2
        have hcompl : ({i, j, k} : Finset (Fin n))ᶜ.card = n - 3 := by
          rw [Finset.card_compl, Fintype.card_fin, hcard]
        rcases g2 (by omega) with h' | h' <;> omega

set_option maxHeartbeats 800000 in
open Classical in
/-- **Burls have at least two vertices.** -/
theorem ep_burl_two_le {W E : Type*} [Fintype E] (α β : E → W) (L X : Finset W)
    (h : EpCubicD α β L) (hXL : X ⊆ L) (hburl : EpBurl α β X) : 2 ≤ X.card := by
  by_contra hlt
  have hnl : ∀ g, α g ∈ L → α g ≠ β g := by
    intro g hg
    rcases h.1 g with h' | h'
    · exact h'.2.2
    · exact absurd hg h'.1
  -- no flip sets
  have hzero : ∀ N : Finset E, epAltNum α β X N = 0 := by
    intro N
    by_contra hne
    obtain ⟨D, hDne, hDin, -, -⟩ := epAltNum_spec α β X N
    obtain ⟨g, hg⟩ := hDne ⟨0, Nat.pos_of_ne_zero hne⟩
    obtain ⟨a1, a2⟩ := hDin _ g hg
    have : α g = β g := Finset.card_le_one.mp (by omega) _ a1 _ a2
    exact hnl g (hXL a1) this
  have hsum : ∀ p : Finset E → ℝ, ∑ N, p N * (epAltNum α β X N : ℝ) = 0 := by
    intro p
    apply Finset.sum_eq_zero
    intro N _
    rw [hzero N]; simp
  -- a balanced distribution
  suffices hex : ∃ p : Finset E → ℝ, EpBalanced α β X p by
    obtain ⟨p, hp⟩ := hex
    have := hburl p hp
    rw [hsum p] at this
    norm_num at this
  by_cases hX0 : X = ∅
  · obtain ⟨p, hp⟩ : ∃ p : Finset E → ℝ, ∀ N, p N = if N = ∅ then 1 else 0 := ⟨_, fun _ => rfl⟩
    refine ⟨p, fun N => by rw [hp]; split_ifs <;> norm_num, fun N hN => ?_, ?_, fun e he => ?_⟩
    · have : N = ∅ := by
        by_contra h'
        exact hN (by rw [hp, if_neg h'])
      rw [this, hX0]
      exact ⟨fun e he => absurd he (Finset.notMem_empty e),
        fun c hc => absurd hc (Finset.notMem_empty c)⟩
    · rw [Finset.sum_congr rfl (fun N _ => hp N),
        Finset.sum_ite_eq' Finset.univ ∅ (fun _ => (1 : ℝ))]
      simp
    · rw [hX0] at he
      exact absurd he (fun h' => h'.elim (Finset.notMem_empty _) (Finset.notMem_empty _))
  · obtain ⟨v, hv⟩ : ∃ v, X = {v} := by
      apply Finset.card_eq_one.mp
      have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hX0)
      omega
    subst hv
    have hvL : v ∈ L := hXL (Finset.mem_singleton_self v)
    have hinj : Function.Injective (fun g : E => ({g} : Finset E)) :=
      fun a b hab => Finset.singleton_injective hab
    have hScard : ((epCut α β {v}).image (fun g => ({g} : Finset E))).card = 3 := by
      rw [Finset.card_image_of_injective _ hinj, h.2 v hvL]
    obtain ⟨p, hp⟩ : ∃ p : Finset E → ℝ, ∀ N, p N =
        if N ∈ (epCut α β {v}).image (fun g => ({g} : Finset E)) then 1 / 3 else 0 :=
      ⟨_, fun _ => rfl⟩
    refine ⟨p, fun N => by rw [hp]; split_ifs <;> norm_num, fun N hN => ?_, ?_, fun e he => ?_⟩
    · have hNS : N ∈ (epCut α β {v}).image (fun g => ({g} : Finset E)) := by
        by_contra h'
        exact hN (by rw [hp, if_neg h'])
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hNS
      rw [mem_epCut] at hg
      refine ⟨fun e he => ?_, fun c hc => ?_⟩
      · rw [Finset.mem_singleton.mp he]
        rw [epCross_singleton] at hg
        rcases hg with ⟨a1, -⟩ | ⟨-, a2⟩
        · exact Or.inl (by rw [a1]; exact Finset.mem_singleton_self v)
        · exact Or.inr (by rw [a2]; exact Finset.mem_singleton_self v)
      · rw [Finset.mem_singleton.mp hc]
        exact ⟨g, ⟨Finset.mem_singleton_self g, hg⟩, fun e he => Finset.mem_singleton.mp he.1⟩
    · rw [Finset.sum_congr rfl (fun N _ => hp N), ← Finset.sum_filter, Finset.sum_const,
        Finset.filter_mem_eq_inter, Finset.univ_inter, hScard]
      norm_num
    · have hecr : e ∈ epCut α β {v} := by
        rw [mem_epCut, epCross_singleton]
        simp only [Finset.mem_singleton] at he
        rcases he with h' | h'
        · exact Or.inl ⟨h', fun h'' => hnl e (h' ▸ hvL) (h'.trans h''.symm)⟩
        · have hne : α e ≠ β e := by
            rcases h.1 e with l | l
            · exact l.2.2
            · exact absurd (l.2 ▸ h' ▸ hvL) l.1
          exact Or.inr ⟨fun h'' => hne (h''.trans h'.symm), h'⟩
      rw [Finset.sum_eq_single ({e} : Finset E)]
      · rw [hp, if_pos (Finset.mem_image.mpr ⟨e, hecr, rfl⟩)]
        unfold epInd
        rw [if_pos (Finset.mem_singleton_self e)]
        norm_num
      · intro N _ hNe
        rw [hp]
        by_cases hNS : N ∈ (epCut α β {v}).image (fun g => ({g} : Finset E))
        · obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hNS
          unfold epInd
          rw [if_neg (fun h' : e ∈ ({g} : Finset E) => hNe (by rw [Finset.mem_singleton.mp h']))]
          simp
        · rw [if_neg hNS]; simp
      · intro h'; exact absurd (Finset.mem_univ _) h'

open Classical in
/-- A foliage of maximum weight exists. -/
theorem ep_fw_max {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) :
    ∃ 𝒳₀, EpFol0 α β L 𝒳₀ ∧ ∀ 𝒳, EpFol0 α β L 𝒳 → epFw α β 𝒳 ≤ epFw α β 𝒳₀ := by
  have hne : (L.powerset.powerset.filter (fun 𝒳 => EpFol0 α β L 𝒳)).Nonempty :=
    ⟨∅, Finset.mem_filter.mpr ⟨by simp, fun X hX => absurd hX (Finset.notMem_empty X),
      fun X hX => absurd hX (Finset.notMem_empty X)⟩⟩
  obtain ⟨𝒳₀, h₀, hmax⟩ := Finset.exists_max_image _ (fun 𝒳 => epFw α β 𝒳) hne
  refine ⟨𝒳₀, (Finset.mem_filter.mp h₀).2, fun 𝒳 h𝒳 => hmax 𝒳 (Finset.mem_filter.mpr ⟨?_, h𝒳⟩)⟩
  rw [Finset.mem_powerset]
  intro X hX
  rw [Finset.mem_powerset]
  exact (h𝒳.1 X hX).1

open Classical in
/-- A rootless foliage of a 3-cut contraction whose members avoid the new vertex is a foliage
of the multigraph of the same weight, disjoint from the contracted set. -/
lemma ep_fol0_lift_eq {W E : Type*} [Fintype E] (α β : E → W) (L X : Finset W) (x₀ x₁ : W)
    (h : EpCubicD α β L) (hXL : X ⊆ L) (hx₀ : x₀ ∈ X) (hx₁ : x₁ ∈ X)
    (𝒳 : Finset (Finset W))
    (hfol : EpFol0 (epConA α β X x₀ x₁) (epConB α β X x₀ x₁) (epL' L X x₀) 𝒳)
    (havoid : ∀ Z ∈ 𝒳, x₀ ∉ Z) :
    EpFol0 α β L 𝒳 ∧ (∀ Z ∈ 𝒳, ∀ w, w ∈ Z → w ∉ X) ∧
      epFw α β 𝒳 = epFw (epConA α β X x₀ x₁) (epConB α β X x₀ x₁) 𝒳 := by
  have hZ : ∀ Z ∈ 𝒳, Z ⊆ L ∧ ∀ w, w ∈ Z → w ∉ X := by
    intro Z hZ
    have hsub := (hfol.1 Z hZ).1
    have key : ∀ w, w ∈ Z → w ∈ L ∧ w ∉ X := by
      intro w hw
      have := hsub hw
      unfold epL' at this
      rcases Finset.mem_insert.mp this with h' | h'
      · exact absurd (h' ▸ hw) (havoid Z hZ)
      · exact Finset.mem_sdiff.mp h'
    exact ⟨fun w hw => (key w hw).1, fun w hw => (key w hw).2⟩
  have hb : ∀ Z ∈ 𝒳, EpBurl α β Z ∧ (epCut α β Z).card =
      (epCut (epConA α β X x₀ x₁) (epConB α β X x₀ x₁) Z).card := fun Z hZ' =>
    epCon_burl α β L X Z x₀ x₁ h hXL hx₀ hx₁ (hZ Z hZ').1 (hZ Z hZ').2 (hfol.1 Z hZ').2
  refine ⟨⟨fun Z hZ' => ⟨(hZ Z hZ').1, (hb Z hZ').1⟩, hfol.2⟩, fun Z hZ' => (hZ Z hZ').2, ?_⟩
  unfold epFw
  refine Finset.sum_congr rfl fun Z hZ' => ?_
  have : EpTwig α β Z ↔ EpTwig (epConA α β X x₀ x₁) (epConB α β X x₀ x₁) Z := by
    unfold EpTwig; rw [(hb Z hZ').2]
  by_cases ht : EpTwig α β Z
  · rw [if_pos ht, if_pos (this.mp ht)]
  · rw [if_neg ht, if_neg (fun h' => ht (this.mpr h'))]

lemma EpHasCore.six_le {W E : Type*} [Fintype E] {α β : E → W} {L : Finset W}
    (h : EpCubicD α β L) (hb : EpBridgeless α β L) (hconn : EpConnected α β L)
    (hc : EpHasCore α β L) : 6 ≤ L.card := by
  obtain ⟨α', β', L', hr, -, h6⟩ := hc
  exact h6.trans (Finset.card_le_card (hr.preserves h hb hconn).2.2.2)

set_option maxHeartbeats 1600000 in
open Classical in
/-- **Re-pruning.** A multigraph with a core that is pruned away from a vertex becomes pruned
after contracting at most one irrelevant triangle, and keeps its core; foliages lift without
loss. -/
theorem ep_reprune {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (r : W)
    (h : EpCubicD α β L) (hb : EpBridgeless α β L) (hconn : EpConnected α β L)
    (hpr : EpPrunedAt α β L r) (hc : EpHasCore α β L) :
    ∃ (α' β' : E → W) (L' : Finset W), EpReach α β L α' β' L' ∧ EpPruned α' β' L' ∧
      EpHasCore α' β' L' ∧ L.card ≤ L'.card + 2 ∧ L'.card ≤ L.card ∧
      ∀ 𝒳', EpFol0 α' β' L' 𝒳' → ∃ 𝒳, EpFol0 α β L 𝒳 ∧ epFw α' β' 𝒳' ≤ epFw α β 𝒳 := by
  by_cases hp : EpPruned α β L
  · exact ⟨α, β, L, Relation.ReflTransGen.refl, hp, hc, by omega, le_refl _,
      fun 𝒳' h' => ⟨𝒳', h', le_refl _⟩⟩
  · unfold EpPruned at hp
    push_neg at hp
    obtain ⟨x, y, z, e1, e2, e3, ht, hirr⟩ := hp
    have h6 := hc.six_le h hb hconn
    obtain ⟨hTL, hT3, hTcut⟩ := ep_triangle_cut α β L h hb hconn (by omega) x y z e1 e2 e3 ht
    have hxT : x ∈ ({x, y, z} : Finset W) := Finset.mem_insert_self _ _
    have hyT : y ∈ ({x, y, z} : Finset W) := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    have hxy : x ≠ y := ht.2.2.2.1
    have hrT : r ∈ ({x, y, z} : Finset W) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases hpr x y z e1 e2 e3 ht hirr with h' | h' | h'
      · exact Or.inl h'.symm
      · exact Or.inr (Or.inl h'.symm)
      · exact Or.inr (Or.inr h'.symm)
    have hstep : EpStep α β L (epConA α β ({x, y, z} : Finset W) x y)
        (epConB α β ({x, y, z} : Finset W) x y) (epL' L ({x, y, z} : Finset W) x) :=
      Or.inl ⟨_, x, y, hTL, hxT, hyT, hxy.symm, hTcut, rfl, rfl, rfl⟩
    obtain ⟨h₁, hb₁, hconn₁, -, -⟩ := hstep.preserves h hb hconn
    have hcard : (epL' L ({x, y, z} : Finset W) x).card + 2 = L.card := by
      have e1' := Finset.card_sdiff_add_card_eq_card hTL
      have e2' : (epL' L ({x, y, z} : Finset W) x).card = (L \ ({x, y, z} : Finset W)).card + 1 :=
        Finset.card_insert_of_notMem (fun h' => (Finset.mem_sdiff.mp h').2 hxT)
      omega
    refine ⟨epConA α β ({x, y, z} : Finset W) x y, epConB α β ({x, y, z} : Finset W) x y,
      epL' L ({x, y, z} : Finset W) x, Relation.ReflTransGen.single hstep, ?_, ?_, by omega, by omega,
      fun 𝒳' hfol' => ep_fol_tri_lift α β L x y z e1 e2 e3 h ht hTcut 𝒳' hfol'⟩
    · -- pruned
      intro p q s f1 f2 f3 ht₁ hirr₁
      obtain ⟨a1, a2, a3, -⟩ := ep_tri_contract_triangle α β L x y z hxy.symm hirr
        p q s f1 f2 f3 ht₁
      obtain ⟨ht₂, hpT, hqT, hsT⟩ := epCon_triangle_back α β L ({x, y, z} : Finset W) x y hxT hyT
        p q s f1 f2 f3 ht₁ a1 a2 a3
      by_cases hirr₂ : EpIrrelevant α β p q s
      · rcases hpr p q s f1 f2 f3 ht₂ hirr₂ with h' | h' | h'
        · exact hpT (h' ▸ hrT)
        · exact hqT (h' ▸ hrT)
        · exact hsT (h' ▸ hrT)
      · exact epCon_relevant α β L ({x, y, z} : Finset W) x y h hxT p q s f1 f2 f3 ht₂ hpT hqT hsT
          hirr₂ hirr₁
    · -- still has a core
      obtain ⟨n, Z, hZ⟩ := ep_corePart_of_core α β L h hb hconn hc
      obtain ⟨i, hi1, hi2, hi3⟩ := ep_corePart_triangle α β L n Z hZ x y z e1 e2 e3 ht
      have hTZ : ({x, y, z} : Finset W) ⊆ Z i := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl <;> assumption
      have hZ₁ := ep_corePart_contract α β L ({x, y, z} : Finset W) x y n Z hZ i hTZ hxT
      exact ep_core_of_corePart _ _ _ _ n _ rfl h₁ hb₁ hconn₁ hZ₁

open Classical in
/-- The union of two rootless foliages whose members are pairwise disjoint. -/
lemma ep_fol0_union {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (𝒳 𝒯 : Finset (Finset W)) (h1 : EpFol0 α β L 𝒳) (h2 : EpFol0 α β L 𝒯)
    (hne : ∀ T ∈ 𝒯, T.Nonempty) (hd : ∀ Z ∈ 𝒳, ∀ T ∈ 𝒯, Disjoint Z T) :
    EpFol0 α β L (𝒳 ∪ 𝒯) ∧ epFw α β (𝒳 ∪ 𝒯) = epFw α β 𝒳 + epFw α β 𝒯 := by
  have hdis : Disjoint 𝒳 𝒯 := by
    rw [Finset.disjoint_left]
    intro Z hZ hZ'
    obtain ⟨w, hw⟩ := hne Z hZ'
    exact Finset.disjoint_left.mp (hd Z hZ Z hZ') hw hw
  refine ⟨⟨fun X hX => ?_, fun X hX X' hX' hXX' => ?_⟩, ?_⟩
  · rcases Finset.mem_union.mp hX with h' | h'
    · exact h1.1 X h'
    · exact h2.1 X h'
  · rcases Finset.mem_union.mp hX with a | a <;> rcases Finset.mem_union.mp hX' with b | b
    · exact h1.2 X a X' b hXX'
    · exact hd X a X' b
    · exact (hd X' b X a).symm
    · exact h2.2 X a X' b hXX'
  · unfold epFw
    exact Finset.sum_union hdis

set_option maxHeartbeats 1600000 in
open Classical in
/-- **Lemma 13, Case 2a.** `G` pruned with a core partition; a blob `Z i₀` with at least two
vertices whose side graph (the contraction of its complement) has a core. -/
theorem ep_l13_case2a {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (h : EpCubicD α β L) (hb : EpBridgeless α β L) (hconn : EpConnected α β L)
    (hpr : EpPruned α β L) (n : ℕ) (Z : Fin n → Finset W) (hZ : EpCorePart α β L n Z)
    (i₀ : Fin n) (x₀ x₁ y₀ y₁ : W) (hx₀ : x₀ ∈ Z i₀) (hx₁ : x₁ ∈ Z i₀) (hx : x₁ ≠ x₀)
    (hy₀ : y₀ ∈ L \ Z i₀) (hy₁ : y₁ ∈ L \ Z i₀) (hy : y₁ ≠ y₀)
    (hrich : EpHasCore (epConA α β (L \ Z i₀) y₀ y₁) (epConB α β (L \ Z i₀) y₀ y₁)
      (epL' L (L \ Z i₀) y₀))
    (IH : ∀ (α₁ β₁ : E → W) (L₁ : Finset W), L₁.card < L.card → EpCubicD α₁ β₁ L₁ →
      EpBridgeless α₁ β₁ L₁ → EpConnected α₁ β₁ L₁ → EpPruned α₁ β₁ L₁ → EpHasCore α₁ β₁ L₁ →
      EpL13 α₁ β₁ L₁) : EpL13 α β L := by
  intro F hF g hg
  obtain ⟨hXne, hXL, hXcut⟩ := hZ.2.1 i₀
  have hYL : L \ Z i₀ ⊆ L := Finset.sdiff_subset
  have hYcut : (epCut α β (L \ Z i₀)).card = 3 := by
    have : epCut α β (L \ Z i₀) = epCut α β (Z i₀) := by
      ext g'; rw [mem_epCut, mem_epCut]
      exact epD_cross_compl α β L (Z i₀) (L \ Z i₀) h (fun w => Finset.mem_sdiff) g'
    rw [this]; exact hXcut
  -- the contraction of the blob
  have hstep₁ : EpStep α β L (epConA α β (Z i₀) x₀ x₁) (epConB α β (Z i₀) x₀ x₁)
      (epL' L (Z i₀) x₀) := Or.inl ⟨Z i₀, x₀, x₁, hXL, hx₀, hx₁, hx, hXcut, rfl, rfl, rfl⟩
  obtain ⟨h₁, hb₁, hconn₁, -, -⟩ := hstep₁.preserves h hb hconn
  have hZ₁ := ep_corePart_contract α β L (Z i₀) x₀ x₁ n Z hZ i₀ (Finset.Subset.refl _) hx₀
  have hcore₁ := ep_core_of_corePart _ _ _ _ n _ rfl h₁ hb₁ hconn₁ hZ₁
  have hpr₁ : EpPruned (epConA α β (Z i₀) x₀ x₁) (epConB α β (Z i₀) x₀ x₁) (epL' L (Z i₀) x₀) := by
    intro p q s f1 f2 f3 ht hirr
    obtain ⟨i, hi1, hi2, hi3⟩ := ep_corePart_triangle _ _ _ n _ hZ₁ p q s f1 f2 f3 ht
    have hpq : p ≠ q := ht.2.2.2.1
    by_cases hii : i = i₀
    · simp only [hii, if_true, Finset.sdiff_self, Finset.mem_insert, Finset.notMem_empty,
        or_false] at hi1 hi2
      exact hpq (hi1.trans hi2.symm)
    · simp only [hii, if_false] at hi1 hi2 hi3
      have hno : ∀ w, w ∈ Z i → w ≠ x₀ := fun w hw h' =>
        Finset.disjoint_left.mp (hZ.2.2.1 i i₀ hii) hw (h' ▸ hx₀)
      obtain ⟨ht', hpX, hqX, hsX⟩ := epCon_triangle_back α β L (Z i₀) x₀ x₁ hx₀ hx₁ p q s f1 f2 f3
        ht (hno p hi1) (hno q hi2) (hno s hi3)
      exact epCon_relevant α β L (Z i₀) x₀ x₁ h hx₀ p q s f1 f2 f3 ht' hpX hqX hsX
        (hpr p q s f1 f2 f3 ht') hirr
  -- the side graph of the blob
  have hstep₂ : EpStep α β L (epConA α β (L \ Z i₀) y₀ y₁) (epConB α β (L \ Z i₀) y₀ y₁)
      (epL' L (L \ Z i₀) y₀) := Or.inl ⟨L \ Z i₀, y₀, y₁, hYL, hy₀, hy₁, hy, hYcut, rfl, rfl, rfl⟩
  obtain ⟨h₂, hb₂, hconn₂, -, -⟩ := hstep₂.preserves h hb hconn
  have hpr₂ : EpPrunedAt (epConA α β (L \ Z i₀) y₀ y₁) (epConB α β (L \ Z i₀) y₀ y₁)
      (epL' L (L \ Z i₀) y₀) y₀ := by
    intro p q s f1 f2 f3 ht hirr
    by_contra hcon
    push_neg at hcon
    obtain ⟨ht', hpX, hqX, hsX⟩ := epCon_triangle_back α β L (L \ Z i₀) y₀ y₁ hy₀ hy₁ p q s
      f1 f2 f3 ht hcon.1 hcon.2.1 hcon.2.2
    exact epCon_relevant α β L (L \ Z i₀) y₀ y₁ h hy₀ p q s f1 f2 f3 ht' hpX hqX hsX
      (hpr p q s f1 f2 f3 ht') hirr
  obtain ⟨α₂, β₂, L₂, hreach₂, hpr₂', hcore₂, hc1, hc2, hlift₂⟩ :=
    ep_reprune _ _ _ y₀ h₂ hb₂ hconn₂ hpr₂ hrich
  obtain ⟨h₂', hb₂', hconn₂', -⟩ := hreach₂.preserves h₂ hb₂ hconn₂
  -- sizes
  have hcX := Finset.card_sdiff_add_card_eq_card hXL
  have hcard₁ : (epL' L (Z i₀) x₀).card + (Z i₀).card = L.card + 1 := by
    have e2 : (epL' L (Z i₀) x₀).card = (L \ Z i₀).card + 1 :=
      Finset.card_insert_of_notMem (fun h' => (Finset.mem_sdiff.mp h').2 hx₀)
    omega
  have hcard₂ : (epL' L (L \ Z i₀) y₀).card = (Z i₀).card + 1 := by
    have e2 : (epL' L (L \ Z i₀) y₀).card = (L \ (L \ Z i₀)).card + 1 :=
      Finset.card_insert_of_notMem (fun h' => (Finset.mem_sdiff.mp h').2 hy₀)
    have e3 := Finset.card_sdiff_add_card_eq_card hYL
    omega
  have hX2 : 2 ≤ (Z i₀).card := by
    have : ({x₀, x₁} : Finset W) ⊆ Z i₀ := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact hx₀
      · rw [Finset.mem_singleton.mp hw]; exact hx₁
    have := Finset.card_le_card this
    rw [Finset.card_pair hx.symm] at this
    exact this
  have hY2 : 2 ≤ (L \ Z i₀).card := by
    have : ({y₀, y₁} : Finset W) ⊆ L \ Z i₀ := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact hy₀
      · rw [Finset.mem_singleton.mp hw]; exact hy₁
    have := Finset.card_le_card this
    rw [Finset.card_pair hy.symm] at this
    exact this
  -- maximal foliages and their lifts
  obtain ⟨𝒳₁, hfol₁, hmax₁⟩ := ep_fw_max (epConA α β (Z i₀) x₀ x₁) (epConB α β (Z i₀) x₀ x₁)
    (epL' L (Z i₀) x₀)
  obtain ⟨𝒳₂, hfol₂, hmax₂⟩ := ep_fw_max α₂ β₂ L₂
  obtain ⟨d1, w1⟩ := ep_fol0_drop _ _ _ 𝒳₁ hfol₁ x₀
  obtain ⟨l1, l2, l3⟩ := ep_fol0_lift_eq α β L (Z i₀) x₀ x₁ h hXL hx₀ hx₁ _ d1
    (fun T hT => (Finset.mem_filter.mp hT).2)
  obtain ⟨𝒳₂b, hfol₂b, hw₂b⟩ := hlift₂ 𝒳₂ hfol₂
  obtain ⟨d2, w2⟩ := ep_fol0_drop _ _ _ 𝒳₂b hfol₂b y₀
  obtain ⟨m1, m2, m3⟩ := ep_fol0_lift_eq α β L (L \ Z i₀) y₀ y₁ h hYL hy₀ hy₁ _ d2
    (fun T hT => (Finset.mem_filter.mp hT).2)
  obtain ⟨u1, u2⟩ := ep_fol0_union α β L _ _ l1 m1
    (fun T hT => Finset.card_pos.mp (by
      have := ep_burl_two_le α β L T h (m1.1 T hT).1 (m1.1 T hT).2; omega))
    (fun A hA B hB => by
      rw [Finset.disjoint_left]
      intro w hwA hwB
      exact m2 B hB w hwB (Finset.mem_sdiff.mpr ⟨(l1.1 A hA).1 hwA, l2 A hA w hwA⟩))
  have hFsum : epFw (epConA α β (Z i₀) x₀ x₁) (epConB α β (Z i₀) x₀ x₁) 𝒳₁ + epFw α₂ β₂ 𝒳₂ ≤
      F + 2 * (196 / 995) := by
    have := hF _ u1
    rw [u2, l3, m3] at this
    linarith
  -- the two induction hypotheses
  have ih₁ := IH _ _ _ (by omega) h₁ hb₁ hconn₁ hpr₁ hcore₁ _ hmax₁
  have ih₂ := IH α₂ β₂ L₂ (by omega) h₂' hb₂' hconn₂' hpr₂' hcore₂ _ hmax₂
  have hk₂ : ∀ g', epConA α β (Z i₀) x₀ x₁ g' ∈ epL' L (Z i₀) x₀ →
      ⌈(2 : ℝ) ^ (((epL' L (Z i₀) x₀).card : ℝ) / 995 -
        epFw (epConA α β (Z i₀) x₀ x₁) (epConB α β (Z i₀) x₀ x₁) 𝒳₁ + 396 / 995)⌉₊ ≤
        epMe (epConA α β (Z i₀) x₀ x₁) (epConB α β (Z i₀) x₀ x₁) (epL' L (Z i₀) x₀) g' :=
    fun g' hg' => Nat.ceil_le.mpr (ih₁ g' hg')
  have hk₁ : ∀ g', epConA α β (L \ Z i₀) y₀ y₁ g' ∈ epL' L (L \ Z i₀) y₀ →
      ⌈(2 : ℝ) ^ ((L₂.card : ℝ) / 995 - epFw α₂ β₂ 𝒳₂ + 396 / 995)⌉₊ ≤
        epMe (epConA α β (L \ Z i₀) y₀ y₁) (epConB α β (L \ Z i₀) y₀ y₁)
          (epL' L (L \ Z i₀) y₀) g' :=
    fun g' hg' => EpReach.mstar_le hreach₂ h₂ hb₂ hconn₂ _
      (fun g'' hg'' => Nat.ceil_le.mpr (ih₂ g'' hg'')) g' hg'
  have hprod := ep3_mstar α β L (Z i₀) (L \ Z i₀) x₀ x₁ y₀ y₁ h hXL (fun w => Finset.mem_sdiff)
    hx₀ hy₀ _ _ hk₁ hk₂ g hg
  have hreal : ((⌈(2 : ℝ) ^ ((L₂.card : ℝ) / 995 - epFw α₂ β₂ 𝒳₂ + 396 / 995)⌉₊ : ℝ) *
      (⌈(2 : ℝ) ^ (((epL' L (Z i₀) x₀).card : ℝ) / 995 -
        epFw (epConA α β (Z i₀) x₀ x₁) (epConB α β (Z i₀) x₀ x₁) 𝒳₁ + 396 / 995)⌉₊ : ℝ)) ≤
      (epMe α β L g : ℝ) := by exact_mod_cast hprod
  have hsizes : (L.card : ℝ) ≤ (epL' L (Z i₀) x₀).card + L₂.card := by
    exact_mod_cast (by omega : L.card ≤ (epL' L (Z i₀) x₀).card + L₂.card)
  calc (2 : ℝ) ^ ((L.card : ℝ) / 995 - F + 396 / 995)
      ≤ (2 : ℝ) ^ (((L₂.card : ℝ) / 995 - epFw α₂ β₂ 𝒳₂ + 396 / 995) +
          (((epL' L (Z i₀) x₀).card : ℝ) / 995 -
            epFw (epConA α β (Z i₀) x₀ x₁) (epConB α β (Z i₀) x₀ x₁) 𝒳₁ + 396 / 995)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        linarith
    _ = (2 : ℝ) ^ ((L₂.card : ℝ) / 995 - epFw α₂ β₂ 𝒳₂ + 396 / 995) *
          (2 : ℝ) ^ (((epL' L (Z i₀) x₀).card : ℝ) / 995 -
            epFw (epConA α β (Z i₀) x₀ x₁) (epConB α β (Z i₀) x₀ x₁) 𝒳₁ + 396 / 995) :=
        Real.rpow_add (by norm_num) _ _
    _ ≤ _ := le_trans (mul_le_mul (Nat.le_ceil _) (Nat.le_ceil _)
        (Real.rpow_nonneg (by norm_num) _) (Nat.cast_nonneg _)) hreal

open Classical in
/-- Distinct blobs of a core partition are joined by at most one edge. -/
lemma ep_corePart_btw_le {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (n : ℕ)
    (Z : Fin n → Finset W) (hZ : EpCorePart α β L n Z) (i j : Fin n) (hij : i ≠ j) :
    (epBtw α β (Z i) (Z j)).card ≤ 1 := by
  obtain ⟨h6, hblob, hdis, hcov, hun⟩ := hZ
  have e := ep_cut_union α β (Z i) (Z j) (hdis i j hij)
  rw [(hblob i).2.2, (hblob j).2.2] at e
  have hI : ({i, j} : Finset (Fin n)).biUnion Z = Z i ∪ Z j := by
    ext w; simp [Finset.mem_biUnion]
  have hcard : ({i, j} : Finset (Fin n)).card = 2 := Finset.card_pair hij
  have := (hun {i, j} ⟨i, Finset.mem_insert_self _ _⟩ (fun h' => by
    rw [h', Finset.card_univ, Fintype.card_fin] at hcard; omega)).1
  rw [hI] at this
  omega

open Classical in
/-- No three blobs of a core partition are pairwise joined by edges. -/
lemma ep_corePart_no_three {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W) (n : ℕ)
    (Z : Fin n → Finset W) (hZ : EpCorePart α β L n Z) (i j k : Fin n) (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) (p1 : 0 < (epBtw α β (Z i) (Z j)).card)
    (p2 : 0 < (epBtw α β (Z j) (Z k)).card) (p3 : 0 < (epBtw α β (Z i) (Z k)).card) : False := by
  obtain ⟨h6, hblob, hdis, hcov, hun⟩ := hZ
  have u1 := ep_cut_union α β (Z j) (Z k) (hdis j k hjk)
  rw [(hblob j).2.2, (hblob k).2.2] at u1
  have hd : Disjoint (Z i) (Z j ∪ Z k) :=
    Finset.disjoint_union_right.mpr ⟨hdis i j hij, hdis i k hik⟩
  have u2 := ep_cut_union α β (Z i) (Z j ∪ Z k) hd
  rw [(hblob i).2.2] at u2
  have u3 := ep_btw_add α β (Z i) (Z j) (Z k) (hdis i j hij) (hdis i k hik) (hdis j k hjk)
  have hI : ({i, j, k} : Finset (Fin n)).biUnion Z = Z i ∪ (Z j ∪ Z k) := by
    ext w; simp [Finset.mem_biUnion]
  have hcard : ({i, j, k} : Finset (Fin n)).card = 3 :=
    Finset.card_eq_three.mpr ⟨i, j, k, hij, hik, hjk, rfl⟩
  have hne : ({i, j, k} : Finset (Fin n)) ≠ Finset.univ := fun h' => by
    rw [h', Finset.card_univ, Fintype.card_fin] at hcard; omega
  obtain ⟨g1, g2⟩ := hun {i, j, k} ⟨i, Finset.mem_insert_self _ _⟩ hne
  rw [hI] at g1 g2
  have hcompl : ({i, j, k} : Finset (Fin n))ᶜ.card = n - 3 := by
    rw [Finset.card_compl, Fintype.card_fin, hcard]
  rcases g2 (by omega) with h' | h' <;> omega

set_option maxHeartbeats 1600000 in
open Classical in
/-- **Collapsing a core partition.** Contracting all blobs with at least two vertices gives a
cyclically 4-edge-connected multigraph with one vertex in every blob; a foliage of it whose
members only use vertices of singleton blobs is a foliage of `G` of the same weight. -/
theorem ep_corePart_collapse {W E : Type*} [Fintype E] : ∀ (m : ℕ) (α β : E → W) (L : Finset W)
    (n : ℕ) (Z : Fin n → Finset W), L.card = m → EpCubicD α β L → EpBridgeless α β L →
    EpConnected α β L → EpCorePart α β L n Z →
    ∃ (αc βc : E → W) (Lc : Finset W), EpReach α β L αc βc Lc ∧ EpCyc4 αc βc Lc ∧
      Lc.card = n ∧ Lc ⊆ L ∧ (∀ i, (Lc ∩ Z i).card = 1) ∧
      ∀ 𝒳, EpFol0 αc βc Lc 𝒳 → (∀ T ∈ 𝒳, ∀ w ∈ T, ∀ i, w ∈ Z i → (Z i).card = 1) →
        EpFol0 α β L 𝒳 ∧ epFw α β 𝒳 = epFw αc βc 𝒳 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro α β L n Z hm h hb hconn hZ
    by_cases hall : ∀ i, (Z i).card = 1
    · obtain ⟨h4, hLn⟩ := ep_cyc4_of_corePart α β L h n Z hZ hall
      refine ⟨α, β, L, Relation.ReflTransGen.refl, h4, hLn, Finset.Subset.refl _, fun i => ?_,
        fun 𝒳 hfol _ => ⟨hfol, rfl⟩⟩
      rw [Finset.inter_eq_right.mpr (hZ.2.1 i).2.1]; exact hall i
    · push_neg at hall
      obtain ⟨i₀, hi₀⟩ := hall
      obtain ⟨hne, hsub, hcut⟩ := hZ.2.1 i₀
      obtain ⟨x₀, hx₀, x₁, hx₁, hx⟩ := Finset.one_lt_card.mp (by
        have := Finset.card_pos.mpr hne; omega : 1 < (Z i₀).card)
      have hstep : EpStep α β L (epConA α β (Z i₀) x₀ x₁) (epConB α β (Z i₀) x₀ x₁)
          (epL' L (Z i₀) x₀) :=
        Or.inl ⟨Z i₀, x₀, x₁, hsub, hx₀, hx₁, hx.symm, hcut, rfl, rfl, rfl⟩
      obtain ⟨h₁, hb₁, hconn₁, hL₁L, hlt⟩ := hstep.preserves h hb hconn
      have hZ₁ := ep_corePart_contract α β L (Z i₀) x₀ x₁ n Z hZ i₀ (Finset.Subset.refl _) hx₀
      obtain ⟨αc, βc, Lc, hreach, h4, hcn, hLcL₁, hone, hlift⟩ :=
        ih _ (by omega) _ _ _ n _ rfl h₁ hb₁ hconn₁ hZ₁
      have hZ₁i : ∀ i, i ≠ i₀ →
          (if i = i₀ then insert x₀ (Z i₀ \ Z i₀) else Z i) = Z i := fun i hi => by
        rw [if_neg hi]
      have hZ₁0 : (if i₀ = i₀ then insert x₀ (Z i₀ \ Z i₀) else Z i₀) = {x₀} := by
        rw [if_pos rfl, Finset.sdiff_self]; rfl
      refine ⟨αc, βc, Lc, Relation.ReflTransGen.head hstep hreach, h4, hcn,
        hLcL₁.trans hL₁L, fun i => ?_, fun 𝒳 hfol hin => ?_⟩
      · by_cases hi : i = i₀
        · have := hone i₀
          rw [hZ₁0] at this
          rw [hi]
          have hsub' : Lc ∩ Z i₀ ⊆ Lc ∩ {x₀} := by
            intro w hw
            obtain ⟨hw1, hw2⟩ := Finset.mem_inter.mp hw
            have := hLcL₁ hw1
            unfold epL' at this
            rcases Finset.mem_insert.mp this with h' | h'
            · exact Finset.mem_inter.mpr ⟨hw1, Finset.mem_singleton.mpr h'⟩
            · exact absurd hw2 (Finset.mem_sdiff.mp h').2
          have hsup : Lc ∩ {x₀} ⊆ Lc ∩ Z i₀ := by
            intro w hw
            obtain ⟨hw1, hw2⟩ := Finset.mem_inter.mp hw
            exact Finset.mem_inter.mpr ⟨hw1, (Finset.mem_singleton.mp hw2) ▸ hx₀⟩
          rw [Finset.Subset.antisymm hsub' hsup]; exact this
        · have := hone i
          rw [hZ₁i i hi] at this
          exact this
      · obtain ⟨f1, f2⟩ := hlift 𝒳 hfol (fun T hT w hw i hwi => by
          by_cases hi : i = i₀
          · rw [hi, hZ₁0, Finset.card_singleton]
          · rw [hZ₁i i hi] at hwi ⊢
            exact hin T hT w hw i hwi)
        obtain ⟨l1, -, l3⟩ := ep_fol0_lift_eq α β L (Z i₀) x₀ x₁ h hsub hx₀ hx₁ 𝒳 f1
          (fun T hT hxT => hi₀ (hin T hT x₀ hxT i₀ hx₀))
        exact ⟨l1, l3.trans f2⟩

set_option maxHeartbeats 1600000 in
open Classical in
/-- A set of three vertices with a cut of size three contains a pair with a cut of size two,
or is a triangle. -/
theorem ep_three_set {W E : Type*} [Fintype E] (α β : E → W) (L S : Finset W)
    (h : EpCubicD α β L) (hb : EpBridgeless α β L) (hconn : EpConnected α β L) (hSL : S ⊆ L)
    (hSne : S ≠ L) (hS3 : S.card = 3) (hcut : (epCut α β S).card = 3) :
    (∃ p q, p ∈ S ∧ q ∈ S ∧ p ≠ q ∧ (epCut α β ({p} ∪ {q} : Finset W)).card = 2) ∨
    (∃ x y z e1 e2 e3, S = {x, y, z} ∧ EpTriangle α β L x y z e1 e2 e3) := by
  obtain ⟨x, y, z, hxy, hxz, hyz, hSeq⟩ := Finset.card_eq_three.mp hS3
  have hTmem : ∀ w, w ∈ S ↔ w = x ∨ w = y ∨ w = z := by
    intro w; rw [hSeq]; simp only [Finset.mem_insert, Finset.mem_singleton]
  have hxS : x ∈ S := (hTmem x).mpr (Or.inl rfl)
  have hyS : y ∈ S := (hTmem y).mpr (Or.inr (Or.inl rfl))
  have hzS : z ∈ S := (hTmem z).mpr (Or.inr (Or.inr rfl))
  by_cases hpairs : ∃ p q, p ∈ S ∧ q ∈ S ∧ p ≠ q ∧ (epCut α β ({p} ∪ {q} : Finset W)).card = 2
  · exact Or.inl hpairs
  · right
    push_neg at hpairs
    have hpair : ∀ p q s : W, p ∈ S → q ∈ S → s ∈ S → p ≠ q → p ≠ s → q ≠ s →
        (∀ w, w ∈ S ↔ w = p ∨ w = q ∨ w = s) →
        (epBtw α β {p} {q}).card ≤ 1 ∧
          3 ≤ (epBtw α β {p} {q}).card + (epBtw α β ({p} ∪ {q}) {s}).card := by
      intro p q s hp hq hs hpq hps hqs hmem
      have hd : Disjoint ({p} : Finset W) {q} := Finset.disjoint_singleton.mpr hpq
      have e1 := ep_cut_union α β {p} {q} hd
      rw [h.2 p (hSL hp), h.2 q (hSL hq)] at e1
      have hd2 : Disjoint ({p} ∪ {q} : Finset W) {s} := by
        rw [Finset.disjoint_singleton_right, Finset.mem_union, Finset.mem_singleton,
          Finset.mem_singleton]
        exact fun h' => h'.elim (fun h'' => hps h''.symm) (fun h'' => hqs h''.symm)
      have hSe : ({p} ∪ {q} ∪ {s} : Finset W) = S := by
        ext w
        rw [hmem, Finset.mem_union, Finset.mem_union, Finset.mem_singleton,
          Finset.mem_singleton, Finset.mem_singleton]
        tauto
      have e2 := ep_cut_union α β ({p} ∪ {q}) {s} hd2
      rw [hSe, hcut, h.2 s (hSL hs)] at e2
      have hPS : ({p} ∪ {q} : Finset W) ⊆ S := by
        intro w hw
        rw [Finset.mem_union, Finset.mem_singleton, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl <;> assumption
      have hge := ep_cut_ge_two α β L hb hconn ({p} ∪ {q}) (hPS.trans hSL)
        ⟨p, Finset.mem_union_left _ (Finset.mem_singleton_self p)⟩
        (fun h' => by
          have : s ∈ ({p} ∪ {q} : Finset W) := h' ▸ hSL hs
          exact Finset.disjoint_left.mp hd2 this (Finset.mem_singleton_self s))
      have hne2 := hpairs p q hp hq hpq
      constructor <;> omega
    obtain ⟨p1, p2⟩ := hpair x y z hxS hyS hzS hxy hxz hyz hTmem
    obtain ⟨q1, q2⟩ := hpair y z x hyS hzS hxS hyz (Ne.symm hxy) (Ne.symm hxz)
      (fun w => by rw [hTmem]; tauto)
    obtain ⟨r1, r2⟩ := hpair x z y hxS hzS hyS hxz hxy (Ne.symm hyz)
      (fun w => by rw [hTmem]; tauto)
    have u1 := ep_btw_union_le α β {z} {x} {y}
    rw [ep_btw_comm α β {z} ({x} ∪ {y}), ep_btw_comm α β {z} {x}, ep_btw_comm α β {z} {y}] at u1
    have n1 : 1 ≤ (epBtw α β {x} {y}).card := by omega
    have n2 : 1 ≤ (epBtw α β {y} {z}).card := by omega
    have n3 : 1 ≤ (epBtw α β {x} {z}).card := by omega
    obtain ⟨exy, hexy⟩ := Finset.card_pos.mp n1
    obtain ⟨eyz, heyz⟩ := Finset.card_pos.mp n2
    obtain ⟨exz, hexz⟩ := Finset.card_pos.mp n3
    have hedge : ∀ (p q : W) (e : E), p ≠ q → e ∈ epBtw α β {p} {q} →
        ∀ w, epCross α β {w} e ↔ w = p ∨ w = q := by
      intro p q e hpq he w
      rw [mem_epBtw] at he
      simp only [Finset.mem_singleton] at he
      exact ep_edge_cross α β p q e hpq he w
    exact ⟨x, y, z, exy, eyz, exz, hSeq, hSL hxS, hSL hyS, hSL hzS, hxy, hyz, hxz,
      hedge x y exy hxy hexy, hedge y z eyz hyz heyz, fun w => by
        rw [hedge x z exz hxz hexz w]; exact or_comm⟩

set_option maxHeartbeats 1600000 in
open Classical in
/-- **Foliage inside a blob with a coreless side.** -/
theorem ep_blob_foliage {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (h : EpCubicD α β L) (hb : EpBridgeless α β L) (hconn : EpConnected α β L)
    (hpr : EpPruned α β L) (n : ℕ) (Z : Fin n → Finset W) (hZ : EpCorePart α β L n Z)
    (i : Fin n) (h2 : 2 ≤ (Z i).card)
    (hpoor : ∀ y₀ y₁, y₀ ∈ L \ Z i → y₁ ∈ L \ Z i → y₁ ≠ y₀ →
      ¬EpHasCore (epConA α β (L \ Z i) y₀ y₁) (epConB α β (L \ Z i) y₀ y₁)
        (epL' L (L \ Z i) y₀)) :
    ∃ 𝒳, EpFol0 α β L 𝒳 ∧ (∀ T ∈ 𝒳, T ⊆ Z i) ∧
      ((Z i).card + 1 : ℝ) / 995 + 98 / 995 ≤ epFw α β 𝒳 := by
  obtain ⟨hXne, hXL, hXcut⟩ := hZ.2.1 i
  -- two vertices outside the blob
  obtain ⟨j, hj, k, hk, hjk⟩ := Finset.one_lt_card.mp (by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    have := hZ.1; omega : 1 < ((Finset.univ : Finset (Fin n)).erase i).card)
  obtain ⟨y₀, hy₀j⟩ := (hZ.2.1 j).1
  obtain ⟨y₁, hy₁k⟩ := (hZ.2.1 k).1
  have hji : j ≠ i := Finset.ne_of_mem_erase hj
  have hki : k ≠ i := Finset.ne_of_mem_erase hk
  have hy₀ : y₀ ∈ L \ Z i := Finset.mem_sdiff.mpr ⟨(hZ.2.1 j).2.1 hy₀j,
    fun h' => Finset.disjoint_left.mp (hZ.2.2.1 j i hji) hy₀j h'⟩
  have hy₁ : y₁ ∈ L \ Z i := Finset.mem_sdiff.mpr ⟨(hZ.2.1 k).2.1 hy₁k,
    fun h' => Finset.disjoint_left.mp (hZ.2.2.1 k i hki) hy₁k h'⟩
  have hy : y₁ ≠ y₀ := fun h' => Finset.disjoint_left.mp (hZ.2.2.1 j k hjk) hy₀j (h' ▸ hy₁k)
  have hXneL : Z i ≠ L := fun h' => (Finset.mem_sdiff.mp hy₀).2 (h' ▸ (Finset.mem_sdiff.mp hy₀).1)
  have hYcut : (epCut α β (L \ Z i)).card = 3 := by
    have : epCut α β (L \ Z i) = epCut α β (Z i) := by
      ext g'; rw [mem_epCut, mem_epCut]
      exact epD_cross_compl α β L (Z i) (L \ Z i) h (fun w => Finset.mem_sdiff) g'
    rw [this]; exact hXcut
  by_cases h5 : 5 ≤ (Z i).card
  · have hcard : (epL' L (L \ Z i) y₀).card = (Z i).card + 1 := by
      have e2 : (epL' L (L \ Z i) y₀).card = (L \ (L \ Z i)).card + 1 :=
        Finset.card_insert_of_notMem (fun h' => (Finset.mem_sdiff.mp h').2 hy₀)
      have e3 := Finset.card_sdiff_add_card_eq_card (Finset.sdiff_subset : L \ Z i ⊆ L)
      have e4 := Finset.card_sdiff_add_card_eq_card hXL
      omega
    obtain ⟨𝒳, hfol, havoid, hw⟩ := ep_lemma11_cut α β L (L \ Z i) y₀ y₁ h hb hconn hpr
      Finset.sdiff_subset hy₀ hy₁ hy hYcut (hpoor y₀ y₁ hy₀ hy₁ hy) (by omega)
    refine ⟨𝒳, hfol.toFol0, fun T hT w hwT => ?_, ?_⟩
    · by_contra hwZ
      exact havoid T hT w hwT (Finset.mem_sdiff.mpr ⟨(hfol.1 T hT).1 hwT, hwZ⟩)
    · rw [hcard] at hw
      push_cast at hw
      exact hw
  · have hpar := epD_cut_parity α β L h (Z i) hXL
    have h3 : (Z i).card = 3 := by omega
    rcases ep_three_set α β L (Z i) h hb hconn hXL hXneL h3 hXcut with
      ⟨p, q, hp, hq, hpq, hc2⟩ | ⟨x, y, z, e1, e2, e3, hSeq, ht⟩
    · -- a pair with a cut of size two is a twig
      have hsub : ({p} ∪ {q} : Finset W) ⊆ Z i := by
        intro w hw
        rw [Finset.mem_union, Finset.mem_singleton, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl <;> assumption
      have htw : EpTwig α β ({p} ∪ {q} : Finset W) := Or.inl hc2
      have hburl := ep_twig_burl α β L _ h hb hconn (hsub.trans hXL) y₀
        (Finset.mem_sdiff.mp hy₀).1 (fun h' => (Finset.mem_sdiff.mp hy₀).2 (hsub h')) htw
      refine ⟨{({p} ∪ {q} : Finset W)}, ⟨fun T hT => ?_, fun T hT T' hT' hne => ?_⟩,
        fun T hT => ?_, ?_⟩
      · rw [Finset.mem_singleton.mp hT]; exact ⟨hsub.trans hXL, hburl⟩
      · exact absurd ((Finset.mem_singleton.mp hT).trans (Finset.mem_singleton.mp hT').symm) hne
      · rw [Finset.mem_singleton.mp hT]; exact hsub
      · unfold epFw
        rw [Finset.sum_singleton, if_pos htw, h3]
        norm_num
    · -- a triangle blob is impossible in a pruned multigraph
      exfalso
      have hrel := hpr x y z e1 e2 e3 ht
      unfold EpIrrelevant at hrel
      push_neg at hrel
      obtain ⟨u, hu, v, hv, a, b, haT, hbT, ⟨g, hg⟩, ⟨g', hg'⟩, hab⟩ := hrel
      rw [← hSeq] at hu hv haT hbT
      have hends : ∀ (f : E) (s t : W), s ∈ Z i → t ∉ Z i →
          ((α f = s ∧ β f = t) ∨ (α f = t ∧ β f = s)) →
          ∃ j', j' ≠ i ∧ t ∈ Z j' ∧ f ∈ epBtw α β (Z i) (Z j') := by
        intro f s t hs ht' hf
        have htL : t ∈ L := by
          rcases h.1 f with ⟨l1, l2, -⟩ | ⟨l1, l2⟩
          · rcases hf with ⟨f1, f2⟩ | ⟨f1, f2⟩
            · exact f2 ▸ l2
            · exact f1 ▸ l1
          · rcases hf with ⟨f1, f2⟩ | ⟨f1, f2⟩
            · exact absurd (f1 ▸ hXL hs) l1
            · exact absurd (f2 ▸ hXL hs) (l2 ▸ l1)
        obtain ⟨j', hj'⟩ := hZ.2.2.2.1 t htL
        refine ⟨j', fun h' => ht' (h' ▸ hj'), hj', ?_⟩
        rw [mem_epBtw]
        rcases hf with ⟨f1, f2⟩ | ⟨f1, f2⟩
        · exact Or.inl ⟨f1 ▸ hs, f2 ▸ hj'⟩
        · exact Or.inr ⟨f1 ▸ hj', f2 ▸ hs⟩
      obtain ⟨ja, hja, haj, hgb⟩ := hends g u a hu haT hg
      obtain ⟨jb, hjb, hbj, hgb'⟩ := hends g' v b hv hbT hg'
      by_cases hjj : ja = jb
      · subst hjj
        have hgg : g = g' := by
          by_contra hne
          have : ({g, g'} : Finset E) ⊆ epBtw α β (Z i) (Z ja) := by
            intro f hf
            rcases Finset.mem_insert.mp hf with rfl | hf
            · exact hgb
            · rw [Finset.mem_singleton.mp hf]; exact hgb'
          have := Finset.card_le_card this
          rw [Finset.card_pair hne] at this
          have := ep_corePart_btw_le α β L n Z hZ i ja (Ne.symm hja)
          omega
        subst hgg
        have hau : a ≠ u := fun h' => haT (h' ▸ hu)
        have hbv : b ≠ v := fun h' => hbT (h' ▸ hv)
        have huv : u = v ∧ a = b := by
          rcases hg with ⟨f1, f2⟩ | ⟨f1, f2⟩ <;> rcases hg' with ⟨f3, f4⟩ | ⟨f3, f4⟩
          · exact ⟨f1.symm.trans f3, f2.symm.trans f4⟩
          · exact absurd (f3.symm.trans f1) (fun h' => hbT (h' ▸ hu))
          · exact absurd (f1.symm.trans f3) (fun h' => haT (h' ▸ hv))
          · exact ⟨f2.symm.trans f4, f1.symm.trans f3⟩
        obtain ⟨g'', hg''⟩ := hab (fun h' => absurd huv.1 h')
        have haL : a ∈ L := (hZ.2.1 ja).2.1 haj
        rw [← huv.2] at hg''
        rcases h.1 g'' with ⟨-, -, l3⟩ | ⟨l1, -⟩
        · rcases hg'' with ⟨f1, f2⟩ | ⟨f1, f2⟩ <;> exact l3 (f1.trans f2.symm)
        · rcases hg'' with ⟨f1, f2⟩ | ⟨f1, f2⟩ <;> exact l1 (f1 ▸ haL)
      · have hab' : a ≠ b := fun h' =>
          Finset.disjoint_left.mp (hZ.2.2.1 ja jb hjj) haj (h' ▸ hbj)
        obtain ⟨g'', hg''⟩ := hab (fun _ => hab')
        have hg''b : g'' ∈ epBtw α β (Z ja) (Z jb) := by
          rw [mem_epBtw]
          rcases hg'' with ⟨f1, f2⟩ | ⟨f1, f2⟩
          · exact Or.inl ⟨f1 ▸ haj, f2 ▸ hbj⟩
          · exact Or.inr ⟨f1 ▸ hbj, f2 ▸ haj⟩
        exact ep_corePart_no_three α β L n Z hZ i ja jb (Ne.symm hja) (Ne.symm hjb) hjj
          (Finset.card_pos.mpr ⟨g, hgb⟩) (Finset.card_pos.mpr ⟨g'', hg''b⟩)
          (Finset.card_pos.mpr ⟨g', hgb'⟩)

set_option maxHeartbeats 1600000 in
open Classical in
/-- **Foliages of a cyclically 4-edge-connected multigraph avoiding marked vertices.** Avoiding
`k ≥ 1` marked vertices costs at most `k β₂`. -/
theorem ep_cyc4_fol_avoid {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (h : EpCubicD α β L) (h4 : EpCyc4 α β L) (h6 : 6 ≤ L.card) (R : Finset W) (hRL : R ⊆ L)
    (hR : 1 ≤ R.card) (𝒳 : Finset (Finset W)) (hfol : EpFol0 α β L 𝒳) :
    ∃ 𝒳', EpFol0 α β L 𝒳' ∧ (∀ T ∈ 𝒳', ∀ w ∈ T, w ∉ R) ∧
      epFw α β 𝒳 - (R.card : ℝ) * (98 / 995) ≤ epFw α β 𝒳' := by
  obtain ⟨hb, hconn⟩ := EpCyc4.bridgelessD h h4
  have h2 : ∀ T ∈ 𝒳, 2 ≤ T.card := fun T hT =>
    ep_burl_two_le α β L T h (hfol.1 T hT).1 (hfol.1 T hT).2
  by_cases htw : ∃ T ∈ 𝒳, EpTwig α β T
  · obtain ⟨T, hT, htwT⟩ := htw
    have hTL := (hfol.1 T hT).1
    have hTne : T.Nonempty := Finset.card_pos.mp (by have := h2 T hT; omega)
    have hTneL : T ≠ L := by
      intro h'
      have : epCut α β T = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro g hg
        rw [mem_epCut, h'] at hg
        unfold epCross at hg
        rcases h.1 g with ⟨l1, l2, -⟩ | ⟨l1, l2⟩
        · exact hg.elim (fun h'' => h''.2 l2) (fun h'' => h''.1 l1)
        · rw [l2] at hg; exact hg.elim (fun h'' => h''.2 h''.1) (fun h'' => h''.1 h''.2)
      rcases htwT with h'' | ⟨h'', -⟩ <;> rw [this, Finset.card_empty] at h'' <;> omega
    have h3 := h4.1 T hTL hTne hTneL
    have hT3 : (epCut α β T).card = 3 ∧ 5 ≤ T.card := by
      rcases htwT with h' | h'
      · omega
      · exact h'
    have hco : (L \ T).card = 1 := by
      rcases h4.2 T hTL hT3.1 with h' | h'
      · omega
      · exact h'
    have hall : ∀ T' ∈ 𝒳, T' = T := by
      intro T' hT'
      by_contra hne
      have hd := hfol.2 T' hT' T hT hne
      have : T' ⊆ L \ T := fun w hw =>
        Finset.mem_sdiff.mpr ⟨(hfol.1 T' hT').1 hw, Finset.disjoint_left.mp hd hw⟩
      have := Finset.card_le_card this
      have := h2 T' hT'
      omega
    have h𝒳 : 𝒳 = {T} := by
      ext T'
      rw [Finset.mem_singleton]
      exact ⟨hall T', fun h' => h' ▸ hT⟩
    have hfw : epFw α β 𝒳 = 196 / 995 := by
      rw [h𝒳]; unfold epFw; rw [Finset.sum_singleton, if_pos htwT]
    by_cases hk : R.card = 1
    · obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hk
      have hzL : z ∈ L := hRL (by rw [hz]; exact Finset.mem_singleton_self z)
      have hcut : (epCut α β (L \ {z})).card = 3 := by
        have : epCut α β (L \ {z}) = epCut α β {z} := by
          ext g; rw [mem_epCut, mem_epCut]
          exact epD_cross_compl α β L {z} (L \ {z}) h (fun w => Finset.mem_sdiff) g
        rw [this]; exact h.2 z hzL
      have hcard : (L \ {z}).card + 1 = L.card := by
        have := Finset.card_sdiff_add_card_eq_card (Finset.singleton_subset_iff.mpr hzL)
        rw [Finset.card_singleton] at this
        exact this
      have htw' : EpTwig α β (L \ {z}) := Or.inr ⟨hcut, by omega⟩
      have hzX : z ∉ L \ {z} := fun h' => (Finset.mem_sdiff.mp h').2 (Finset.mem_singleton_self z)
      refine ⟨{L \ {z}}, ⟨fun X hX => ?_, fun X hX X' hX' hne => ?_⟩, fun X hX w hw hwR => ?_, ?_⟩
      · rw [Finset.mem_singleton.mp hX]
        exact ⟨Finset.sdiff_subset, ep_twig_burl α β L _ h hb hconn Finset.sdiff_subset z hzL hzX
          htw'⟩
      · exact absurd ((Finset.mem_singleton.mp hX).trans (Finset.mem_singleton.mp hX').symm) hne
      · rw [Finset.mem_singleton.mp hX] at hw
        rw [hz, Finset.mem_singleton] at hwR
        exact hzX (hwR ▸ hw)
      · rw [hfw, hk]
        unfold epFw
        rw [Finset.sum_singleton, if_pos htw']
        norm_num
    · refine ⟨∅, ⟨fun X hX => absurd hX (Finset.notMem_empty X),
        fun X hX => absurd hX (Finset.notMem_empty X)⟩,
        fun X hX => absurd hX (Finset.notMem_empty X), ?_⟩
      rw [hfw]
      unfold epFw
      rw [Finset.sum_empty]
      have : (2 : ℝ) ≤ R.card := by exact_mod_cast (by omega : 2 ≤ R.card)
      nlinarith
  · push_neg at htw
    refine ⟨𝒳.filter (fun T => ∀ w ∈ T, w ∉ R), ⟨fun X hX => hfol.1 X (Finset.mem_of_mem_filter X hX),
      fun X hX X' hX' hne => hfol.2 X (Finset.mem_of_mem_filter X hX) X'
        (Finset.mem_of_mem_filter X' hX') hne⟩, fun T hT => (Finset.mem_filter.mp hT).2, ?_⟩
    have hdrop : ∀ T, ∃ w, T ∈ 𝒳.filter (fun T => ¬∀ w ∈ T, w ∉ R) → w ∈ T ∧ w ∈ R := by
      intro T
      by_cases hT : T ∈ 𝒳.filter (fun T => ¬∀ w ∈ T, w ∉ R)
      · have := (Finset.mem_filter.mp hT).2
        push_neg at this
        obtain ⟨w, hw1, hw2⟩ := this
        exact ⟨w, fun _ => ⟨hw1, hw2⟩⟩
      · obtain ⟨z₀, -⟩ := Finset.card_pos.mp hR
        exact ⟨z₀, fun h' => absurd h' hT⟩
    choose f hf using hdrop
    have hcard : (𝒳.filter (fun T => ¬∀ w ∈ T, w ∉ R)).card ≤ R.card := by
      refine Finset.card_le_card_of_injOn f (fun T hT => (hf T hT).2) (fun T hT T' hT' hff => ?_)
      by_contra hne
      have hT1 : T ∈ 𝒳.filter (fun T => ¬∀ w ∈ T, w ∉ R) := hT
      have hT1' : T' ∈ 𝒳.filter (fun T => ¬∀ w ∈ T, w ∉ R) := hT'
      have hd := hfol.2 T (Finset.mem_of_mem_filter T hT1) T' (Finset.mem_of_mem_filter T' hT1') hne
      exact Finset.disjoint_left.mp hd (hf T hT1).1 (hff ▸ (hf T' hT1').1)
    unfold epFw
    rw [← Finset.sum_filter_add_sum_filter_not 𝒳 (fun T => ∀ w ∈ T, w ∉ R)]
    have hrest : ∑ T ∈ 𝒳.filter (fun T => ¬∀ w ∈ T, w ∉ R),
        (if EpTwig α β T then (196 : ℝ) / 995 else 98 / 995) =
        ((𝒳.filter (fun T => ¬∀ w ∈ T, w ∉ R)).card : ℝ) * (98 / 995) := by
      rw [Finset.sum_congr rfl (fun T hT => if_neg (htw T (Finset.mem_of_mem_filter T hT))),
        Finset.sum_const, nsmul_eq_mul]
    rw [hrest]
    have : ((𝒳.filter (fun T => ¬∀ w ∈ T, w ∉ R)).card : ℝ) ≤ R.card := by exact_mod_cast hcard
    nlinarith

open Classical in
/-- Union of foliages living in pairwise disjoint sets. -/
lemma ep_fol0_biUnion {W E : Type*} [Fintype E] {ι : Type*} (α β : E → W) (L : Finset W)
    (𝒳 : ι → Finset (Finset W)) (B : ι → Finset W) (I : Finset ι) :
    (∀ i ∈ I, EpFol0 α β L (𝒳 i)) → (∀ i ∈ I, ∀ T ∈ 𝒳 i, T.Nonempty ∧ T ⊆ B i) →
    (∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (B i) (B j)) →
    EpFol0 α β L (I.biUnion 𝒳) ∧ epFw α β (I.biUnion 𝒳) = ∑ i ∈ I, epFw α β (𝒳 i) := by
  induction I using Finset.induction_on with
  | empty =>
    intro _ _ _
    refine ⟨⟨fun X hX => ?_, fun X hX => ?_⟩, ?_⟩
    · rw [Finset.biUnion_empty] at hX; exact absurd hX (Finset.notMem_empty X)
    · rw [Finset.biUnion_empty] at hX; exact absurd hX (Finset.notMem_empty X)
    · unfold epFw; simp
  | insert a s ha ih =>
    intro hfol hin hB
    obtain ⟨f1, f2⟩ := ih (fun i hi => hfol i (Finset.mem_insert_of_mem hi))
      (fun i hi => hin i (Finset.mem_insert_of_mem hi))
      (fun i hi j hj => hB i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    obtain ⟨u1, u2⟩ := ep_fol0_union α β L (𝒳 a) (s.biUnion 𝒳) (hfol a (Finset.mem_insert_self _ _))
      f1
      (fun T hT => by
        obtain ⟨j, hj, hTj⟩ := Finset.mem_biUnion.mp hT
        exact (hin j (Finset.mem_insert_of_mem hj) T hTj).1)
      (fun A hA T hT => by
        obtain ⟨j, hj, hTj⟩ := Finset.mem_biUnion.mp hT
        have hne : a ≠ j := fun h' => ha (h' ▸ hj)
        exact Finset.disjoint_of_subset_left (hin a (Finset.mem_insert_self _ _) A hA).2
          (Finset.disjoint_of_subset_right (hin j (Finset.mem_insert_of_mem hj) T hTj).2
            (hB a (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj) hne)))
    exact ⟨u1, by rw [u2, f2]⟩

set_option maxHeartbeats 1600000 in
open Classical in
/-- **Lemma 13, Case 2b.** `G` pruned with a core partition in which some blob has at least
two vertices and every such blob has a coreless side graph. -/
theorem ep_l13_case2b {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (h : EpCubicD α β L) (hb : EpBridgeless α β L) (hconn : EpConnected α β L)
    (hpr : EpPruned α β L) (n : ℕ) (Z : Fin n → Finset W) (hZ : EpCorePart α β L n Z)
    (i₀ : Fin n) (hi₀ : 2 ≤ (Z i₀).card)
    (hpoor : ∀ i, 2 ≤ (Z i).card → ∀ y₀ y₁, y₀ ∈ L \ Z i → y₁ ∈ L \ Z i → y₁ ≠ y₀ →
      ¬EpHasCore (epConA α β (L \ Z i) y₀ y₁) (epConB α β (L \ Z i) y₀ y₁)
        (epL' L (L \ Z i) y₀))
    (IH : ∀ (α₁ β₁ : E → W) (L₁ : Finset W), L₁.card < L.card → EpCubicD α₁ β₁ L₁ →
      EpBridgeless α₁ β₁ L₁ → EpConnected α₁ β₁ L₁ → EpPruned α₁ β₁ L₁ → EpHasCore α₁ β₁ L₁ →
      EpL13 α₁ β₁ L₁) : EpL13 α β L := by
  intro F hF g hg
  obtain ⟨h6, hblob, hdis, hcov, hun⟩ := hZ
  have hZ' : EpCorePart α β L n Z := ⟨h6, hblob, hdis, hcov, hun⟩
  obtain ⟨αc, βc, Lc, hreach, h4, hcn, hLcL, hone, hlift⟩ :=
    ep_corePart_collapse L.card α β L n Z rfl h hb hconn hZ'
  obtain ⟨hc, hbc, hconnc, -⟩ := hreach.preserves h hb hconn
  -- the number of vertices
  have hLeq : L = Finset.univ.biUnion Z := by
    ext w
    rw [Finset.mem_biUnion]
    exact ⟨fun hw => by obtain ⟨i, hi⟩ := hcov w hw; exact ⟨i, Finset.mem_univ _, hi⟩,
      fun ⟨i, _, hi⟩ => (hblob i).2.1 hi⟩
  have hLcard : L.card = ∑ i, (Z i).card := by
    conv_lhs => rw [hLeq]
    exact Finset.card_biUnion (fun i _ j _ hij => hdis i j hij)
  have hpos : ∀ i, 1 ≤ (Z i).card := fun i => Finset.card_pos.mpr (hblob i).1
  have hLlow : n + 1 ≤ L.card := by
    rw [hLcard]
    have : ∑ i : Fin n, (1 + if i = i₀ then 1 else 0) ≤ ∑ i, (Z i).card := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i = i₀
      · rw [if_pos hi, hi]; omega
      · rw [if_neg hi]; have := hpos i; omega
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Finset.sum_ite_eq' Finset.univ i₀ (fun _ => 1)] at this
    simpa using this
  have hLup : L.card ≤ n + ∑ i ∈ Finset.univ.filter (fun i => 2 ≤ (Z i).card), ((Z i).card + 1) := by
    rw [hLcard]
    have : ∑ i, (Z i).card ≤ ∑ i : Fin n, (1 + if 2 ≤ (Z i).card then (Z i).card + 1 else 0) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : 2 ≤ (Z i).card
      · rw [if_pos hi]; omega
      · rw [if_neg hi]; have := hpos i; omega
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      ← Finset.sum_filter] at this
    simpa using this
  -- the collapsed multigraph
  have hprc : EpPruned αc βc Lc := fun x y z e1 e2 e3 ht _ =>
    ep_cyc4_no_triangle αc βc Lc hc h4 (by omega) x y z e1 e2 e3 ht
  have hcorec : EpHasCore αc βc Lc := ⟨αc, βc, Lc, Relation.ReflTransGen.refl, h4, by omega⟩
  have ihc := IH αc βc Lc (by omega) hc hbc hconnc hprc hcorec
  obtain ⟨𝒳c, hfolc, hmaxc⟩ := ep_fw_max αc βc Lc
  -- the new vertices
  obtain ⟨R, hRdef⟩ : ∃ R : Finset W, R = Lc.filter (fun w => ∃ i, w ∈ Z i ∧ 2 ≤ (Z i).card) :=
    ⟨_, rfl⟩
  have hRmem : ∀ w, w ∈ R ↔ w ∈ Lc ∧ ∃ i, w ∈ Z i ∧ 2 ≤ (Z i).card := by
    intro w; rw [hRdef, Finset.mem_filter]
  have hR1 : 1 ≤ R.card := by
    obtain ⟨w, hw⟩ := Finset.card_pos.mp (by rw [hone i₀]; norm_num : 0 < (Lc ∩ Z i₀).card)
    obtain ⟨hw1, hw2⟩ := Finset.mem_inter.mp hw
    exact Finset.card_pos.mpr ⟨w, (hRmem w).mpr ⟨hw1, i₀, hw2, hi₀⟩⟩
  have hRk : R.card ≤ (Finset.univ.filter (fun i => 2 ≤ (Z i).card)).card := by
    have hidx : ∀ w, ∃ i : Fin n, w ∈ R → (w ∈ Z i ∧ 2 ≤ (Z i).card) := by
      intro w
      by_cases hw : w ∈ R
      · obtain ⟨i, hi⟩ := ((hRmem w).mp hw).2
        exact ⟨i, fun _ => hi⟩
      · exact ⟨i₀, fun h' => absurd h' hw⟩
    choose f hf using hidx
    refine Finset.card_le_card_of_injOn f (fun w hw => ?_) (fun w hw w' hw' hff => ?_)
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hf w hw).2⟩)
    · have hw1 : w ∈ R := hw
      have hw1' : w' ∈ R := hw'
      have m1 : w ∈ Lc ∩ Z (f w) := Finset.mem_inter.mpr ⟨((hRmem w).mp hw1).1, (hf w hw1).1⟩
      have m2 : w' ∈ Lc ∩ Z (f w) := Finset.mem_inter.mpr
        ⟨((hRmem w').mp hw1').1, by rw [hff]; exact (hf w' hw1').1⟩
      exact Finset.card_le_one.mp (by rw [hone (f w)]) w m1 w' m2
  obtain ⟨𝒳', hfol', havoid, hw'⟩ := ep_cyc4_fol_avoid αc βc Lc hc h4 (by omega) R
    (fun w hw => ((hRmem w).mp hw).1) hR1 𝒳c hfolc
  have hin : ∀ T ∈ 𝒳', ∀ w ∈ T, ∀ i, w ∈ Z i → (Z i).card = 1 := by
    intro T hT w hw i hwi
    by_contra hne
    have := hpos i
    exact havoid T hT w hw ((hRmem w).mpr ⟨(hfol'.1 T hT).1 hw, i, hwi, by omega⟩)
  obtain ⟨hfolG, hwG⟩ := hlift 𝒳' hfol' hin
  -- foliages inside the blobs
  have hbl : ∀ i, ∃ 𝒳ᵢ : Finset (Finset W), 2 ≤ (Z i).card →
      (EpFol0 α β L 𝒳ᵢ ∧ (∀ T ∈ 𝒳ᵢ, T ⊆ Z i) ∧
        ((Z i).card + 1 : ℝ) / 995 + 98 / 995 ≤ epFw α β 𝒳ᵢ) := by
    intro i
    by_cases hi : 2 ≤ (Z i).card
    · obtain ⟨𝒳ᵢ, a1, a2, a3⟩ := ep_blob_foliage α β L h hb hconn hpr n Z hZ' i hi (hpoor i hi)
      exact ⟨𝒳ᵢ, fun _ => ⟨a1, a2, a3⟩⟩
    · exact ⟨∅, fun h' => absurd h' hi⟩
  choose 𝒳b h𝒳b using hbl
  obtain ⟨b1, b2⟩ := ep_fol0_biUnion α β L 𝒳b Z (Finset.univ.filter (fun i => 2 ≤ (Z i).card))
    (fun i hi => (h𝒳b i (Finset.mem_filter.mp hi).2).1)
    (fun i hi T hT => by
      have hi' := (Finset.mem_filter.mp hi).2
      refine ⟨Finset.card_pos.mp ?_, (h𝒳b i hi').2.1 T hT⟩
      have := ep_burl_two_le α β L T h ((h𝒳b i hi').1.1 T hT).1 ((h𝒳b i hi').1.1 T hT).2
      omega)
    (fun i _ j _ hij => hdis i j hij)
  obtain ⟨u1, u2⟩ := ep_fol0_union α β L 𝒳' _ hfolG b1
    (fun T hT => by
      obtain ⟨i, hi, hTi⟩ := Finset.mem_biUnion.mp hT
      have hi' := (Finset.mem_filter.mp hi).2
      have := ep_burl_two_le α β L T h ((h𝒳b i hi').1.1 T hTi).1 ((h𝒳b i hi').1.1 T hTi).2
      exact Finset.card_pos.mp (by omega))
    (fun A hA T hT => by
      obtain ⟨i, hi, hTi⟩ := Finset.mem_biUnion.mp hT
      have hi' := (Finset.mem_filter.mp hi).2
      rw [Finset.disjoint_left]
      intro w hwA hwT
      have := hin A hA w hwA i ((h𝒳b i hi').2.1 T hTi hwT)
      omega)
  -- weights
  have hsumb : ((∑ i ∈ Finset.univ.filter (fun i => 2 ≤ (Z i).card), ((Z i).card + 1) : ℕ) : ℝ) / 995 +
      ((Finset.univ.filter (fun i => 2 ≤ (Z i).card)).card : ℝ) * (98 / 995) ≤
      ∑ i ∈ Finset.univ.filter (fun i => 2 ≤ (Z i).card), epFw α β (𝒳b i) := by
    have : ∑ i ∈ Finset.univ.filter (fun i => 2 ≤ (Z i).card),
        (((Z i).card + 1 : ℝ) / 995 + 98 / 995) ≤
        ∑ i ∈ Finset.univ.filter (fun i => 2 ≤ (Z i).card), epFw α β (𝒳b i) :=
      Finset.sum_le_sum (fun i hi => (h𝒳b i (Finset.mem_filter.mp hi).2).2.2)
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.sum_div] at this
    push_cast
    exact this
  have hFG := hF _ u1
  rw [u2, b2, hwG] at hFG
  have hRk' : (R.card : ℝ) ≤ ((Finset.univ.filter (fun i => 2 ≤ (Z i).card)).card : ℝ) := by
    exact_mod_cast hRk
  have hLup' : (L.card : ℝ) ≤ (n : ℝ) +
      ((∑ i ∈ Finset.univ.filter (fun i => 2 ≤ (Z i).card), ((Z i).card + 1) : ℕ) : ℝ) := by
    exact_mod_cast hLup
  have hexp : (L.card : ℝ) / 995 - F + 396 / 995 ≤
      (Lc.card : ℝ) / 995 - epFw αc βc 𝒳c + 396 / 995 := by
    rw [hcn]
    have : (R.card : ℝ) * (98 / 995) ≤
        ((Finset.univ.filter (fun i => 2 ≤ (Z i).card)).card : ℝ) * (98 / 995) :=
      mul_le_mul_of_nonneg_right hRk' (by norm_num)
    have e1 : (L.card : ℝ) / 995 ≤ (n : ℝ) / 995 +
        ((∑ i ∈ Finset.univ.filter (fun i => 2 ≤ (Z i).card), ((Z i).card + 1) : ℕ) : ℝ) / 995 := by
      rw [← add_div]; exact div_le_div_of_nonneg_right hLup' (by norm_num)
    linarith
  have hk : ∀ g', αc g' ∈ Lc →
      ⌈(2 : ℝ) ^ ((Lc.card : ℝ) / 995 - epFw αc βc 𝒳c + 396 / 995)⌉₊ ≤ epMe αc βc Lc g' :=
    fun g' hg' => Nat.ceil_le.mpr (ihc _ hmaxc g' hg')
  have hfin := EpReach.mstar_le hreach h hb hconn _ hk g hg
  calc (2 : ℝ) ^ ((L.card : ℝ) / 995 - F + 396 / 995)
      ≤ (2 : ℝ) ^ ((Lc.card : ℝ) / 995 - epFw αc βc 𝒳c + 396 / 995) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ ≤ (⌈(2 : ℝ) ^ ((Lc.card : ℝ) / 995 - epFw αc βc 𝒳c + 396 / 995)⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ (epMe α β L g : ℝ) := by exact_mod_cast hfin

set_option maxHeartbeats 1600000 in
open Classical in
/-- **Lemma 13.** For a pruned cubic bridgeless connected multigraph with a core, every edge is
in at least `2 ^ (α |L| − F + γ)` perfect matchings, where `F` bounds the weights of the
foliages (`α = 1/995`, `γ = 396/995`). -/
theorem ep_lemma13 {W E : Type*} [Fintype E] : ∀ (m : ℕ) (α β : E → W) (L : Finset W),
    L.card = m → EpCubicD α β L → EpBridgeless α β L → EpConnected α β L → EpPruned α β L →
    EpHasCore α β L → EpL13 α β L := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro α β L hm h hb hconn hpr hcore
    have IH : ∀ (α₁ β₁ : E → W) (L₁ : Finset W), L₁.card < L.card → EpCubicD α₁ β₁ L₁ →
        EpBridgeless α₁ β₁ L₁ → EpConnected α₁ β₁ L₁ → EpPruned α₁ β₁ L₁ → EpHasCore α₁ β₁ L₁ →
        EpL13 α₁ β₁ L₁ := fun α₁ β₁ L₁ hlt h₁ hb₁ hc₁ hp₁ hcore₁ =>
      ih L₁.card (by omega) α₁ β₁ L₁ rfl h₁ hb₁ hc₁ hp₁ hcore₁
    obtain ⟨n, Z, hZ⟩ := ep_corePart_of_core α β L h hb hconn hcore
    by_cases hall : ∀ i, (Z i).card = 1
    · obtain ⟨h4, hLn⟩ := ep_cyc4_of_corePart α β L h n Z hZ hall
      exact ep_l13_cyc4 α β L h h4 (by rw [hLn]; exact hZ.1) IH
    · push_neg at hall
      obtain ⟨i₀, hi₀⟩ := hall
      have hi₀2 : 2 ≤ (Z i₀).card := by
        have := Finset.card_pos.mpr (hZ.2.1 i₀).1; omega
      by_cases h2a : ∃ i, 2 ≤ (Z i).card ∧ ∃ y₀ y₁, y₀ ∈ L \ Z i ∧ y₁ ∈ L \ Z i ∧ y₁ ≠ y₀ ∧
          EpHasCore (epConA α β (L \ Z i) y₀ y₁) (epConB α β (L \ Z i) y₀ y₁)
            (epL' L (L \ Z i) y₀)
      · obtain ⟨i, hi, y₀, y₁, hy₀, hy₁, hy, hrich⟩ := h2a
        obtain ⟨x₀, hx₀, x₁, hx₁, hx⟩ := Finset.one_lt_card.mp (by omega : 1 < (Z i).card)
        exact ep_l13_case2a α β L h hb hconn hpr n Z hZ i x₀ x₁ y₀ y₁ hx₀ hx₁ hx.symm hy₀ hy₁ hy
          hrich IH
      · push_neg at h2a
        exact ep_l13_case2b α β L h hb hconn hpr n Z hZ i₀ hi₀2
          (fun i hi y₀ y₁ hy₀ hy₁ hy => h2a i hi y₀ y₁ hy₀ hy₁ hy) IH

open Classical in
/-- A triangle of a cubic bridgeless multigraph (no hypothesis on the size) has
three vertices and a cut of size three. -/
theorem ep_triangle_cut0 {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (h : EpCubicD α β L) (hb : EpBridgeless α β L) (hconn : EpConnected α β L)
    (x y z : W) (exy eyz ezx : E)
    (ht : EpTriangle α β L x y z exy eyz ezx) :
    ({x, y, z} : Finset W) ⊆ L ∧ ({x, y, z} : Finset W).card = 3 ∧
      (epCut α β ({x, y, z} : Finset W)).card = 3 := by
  obtain ⟨hx, hy, hz, hxy, hyz, hxz, h1, h2, h3⟩ := ht
  have hTeq : ({x, y, z} : Finset W) = ({x} ∪ {y}) ∪ {z} := by
    ext w; simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]; tauto
  have hdxy : Disjoint ({x} : Finset W) {y} := Finset.disjoint_singleton.mpr hxy
  have hdxz : Disjoint ({x} : Finset W) {z} := Finset.disjoint_singleton.mpr hxz
  have hdyz : Disjoint ({y} : Finset W) {z} := Finset.disjoint_singleton.mpr hyz
  have hd2 : Disjoint ({x} ∪ {y} : Finset W) {z} :=
    Finset.disjoint_union_left.mpr ⟨hdxz, hdyz⟩
  have hcard : ({x, y, z} : Finset W).card = 3 := by
    rw [hTeq, Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hdxy,
      Finset.card_singleton, Finset.card_singleton, Finset.card_singleton]
  have hTL : ({x, y, z} : Finset W) ⊆ L := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact hx
    · exact hy
    · exact hz
  refine ⟨hTL, hcard, ?_⟩
  have e1 : 1 ≤ (epBtw α β {x} {y}).card :=
    Finset.card_pos.mpr ⟨exy, ep_edge_btw α β x y exy hxy h1⟩
  have e2 : 1 ≤ (epBtw α β {z} {y}).card :=
    Finset.card_pos.mpr ⟨eyz, by rw [ep_btw_comm]; exact ep_edge_btw α β y z eyz hyz h2⟩
  have e3 : 1 ≤ (epBtw α β {z} {x}).card :=
    Finset.card_pos.mpr ⟨ezx, ep_edge_btw α β z x ezx (Ne.symm hxz) h3⟩
  have c1 := ep_cut_union α β {x} {y} hdxy
  rw [h.2 x hx, h.2 y hy] at c1
  have c2 := ep_cut_union α β ({x} ∪ {y}) {z} hd2
  rw [h.2 z hz, ← hTeq] at c2
  have c3 := ep_btw_add α β {z} {x} {y} hdxz.symm hdyz.symm hdxy
  rw [ep_btw_comm α β {z} ({x} ∪ {y})] at c3
  have c4 := hb _ hTL
  have c5 := epD_cut_parity α β L h _ hTL
  rw [hcard] at c5
  omega

set_option maxHeartbeats 1600000 in
open Classical in
/-- **Lemma 8 with all the data.** Pruning by contractions of irrelevant triangles: the
result is reachable by cut-contractions, pruned, not too small, and its foliages lift without
loss. `New` is a set of vertices lying in no triangle. -/
theorem ep_prune_full {W E : Type*} [Fintype E] : ∀ (n : ℕ) (α β : E → W) (L New : Finset W),
    L.card = n → EpCubicD α β L → EpBridgeless α β L → EpConnected α β L → New ⊆ L →
    (∀ x y z exy eyz ezx, EpTriangle α β L x y z exy eyz ezx → x ∉ New ∧ y ∉ New ∧ z ∉ New) →
    ∃ (α' β' : E → W) (L' : Finset W), EpReach α β L α' β' L' ∧ EpPruned α' β' L' ∧
      3 * New.card + (L \ New).card ≤ 3 * L'.card ∧
      ∀ 𝒳', EpFol0 α' β' L' 𝒳' → ∃ 𝒳, EpFol0 α β L 𝒳 ∧ epFw α' β' 𝒳' ≤ epFw α β 𝒳 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro α β L New hn h hb hconn hNew htri
    by_cases hp : EpPruned α β L
    · refine ⟨α, β, L, Relation.ReflTransGen.refl, hp, ?_, fun 𝒳' h' => ⟨𝒳', h', le_refl _⟩⟩
      have := Finset.card_sdiff_add_card_eq_card hNew
      omega
    · unfold EpPruned at hp
      push_neg at hp
      obtain ⟨x, y, z, exy, eyz, ezx, ht, hirr⟩ := hp
      obtain ⟨hxN, hyN, hzN⟩ := htri x y z exy eyz ezx ht
      obtain ⟨hTL, hT3, hTcut⟩ := ep_triangle_cut0 α β L h hb hconn x y z exy eyz ezx ht
      have hxy : x ≠ y := ht.2.2.2.1
      have hTmem : ∀ w, w ∈ ({x, y, z} : Finset W) ↔ w = x ∨ w = y ∨ w = z := by
        intro w; simp only [Finset.mem_insert, Finset.mem_singleton]
      have hTN : ∀ w, w ∈ ({x, y, z} : Finset W) → w ∉ New := by
        intro w hw
        rcases (hTmem w).mp hw with rfl | rfl | rfl
        · exact hxN
        · exact hyN
        · exact hzN
      have hxT : x ∈ ({x, y, z} : Finset W) := (hTmem x).mpr (Or.inl rfl)
      have hyT : y ∈ ({x, y, z} : Finset W) := (hTmem y).mpr (Or.inr (Or.inl rfl))
      have hstep : EpStep α β L (epConA α β ({x, y, z} : Finset W) x y)
          (epConB α β ({x, y, z} : Finset W) x y) (epL' L ({x, y, z} : Finset W) x) :=
        Or.inl ⟨_, x, y, hTL, hxT, hyT, hxy.symm, hTcut, rfl, rfl, rfl⟩
      obtain ⟨h₁, hb₁, hconn₁, -, -⟩ := hstep.preserves h hb hconn
      have hL₁ : (epL' L ({x, y, z} : Finset W) x).card + 2 = L.card := by
        have e1' := Finset.card_sdiff_add_card_eq_card hTL
        have e2' : (epL' L ({x, y, z} : Finset W) x).card = (L \ ({x, y, z} : Finset W)).card + 1 :=
          Finset.card_insert_of_notMem (fun h' => (Finset.mem_sdiff.mp h').2 hxT)
        omega
      obtain ⟨α', β', L', hreach, hpr, hcount, hlift⟩ :=
        ih (epL' L ({x, y, z} : Finset W) x).card (by omega) _ _ _ (insert x New) rfl h₁ hb₁ hconn₁
          (by
            intro w hw
            unfold epL'
            rcases Finset.mem_insert.mp hw with rfl | hw
            · exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr
                ⟨hNew hw, fun h' => hTN w h' hw⟩))
          (by
            intro p q r e1 e2 e3 ht'
            obtain ⟨a1, a2, a3, a4⟩ := ep_tri_contract_triangle α β L x y z hxy.symm hirr
              p q r e1 e2 e3 ht'
            obtain ⟨b1, b2, b3⟩ := htri p q r e1 e2 e3 a4
            exact ⟨fun h' => (Finset.mem_insert.mp h').elim a1 b1,
              fun h' => (Finset.mem_insert.mp h').elim a2 b2,
              fun h' => (Finset.mem_insert.mp h').elim a3 b3⟩)
      refine ⟨α', β', L', Relation.ReflTransGen.head hstep hreach, hpr, ?_, fun 𝒳' hfol' => ?_⟩
      · have hset : epL' L ({x, y, z} : Finset W) x \ insert x New =
            (L \ New) \ ({x, y, z} : Finset W) := by
          unfold epL'
          ext w
          simp only [Finset.mem_sdiff, Finset.mem_insert]
          constructor
          · rintro ⟨h1 | h1, h2⟩
            · exact absurd (Or.inl h1) h2
            · exact ⟨⟨h1.1, fun h' => h2 (Or.inr h')⟩, h1.2⟩
          · rintro ⟨⟨h1, h2⟩, h3⟩
            exact ⟨Or.inr ⟨h1, h3⟩, fun h' => h'.elim (fun h'' => h3 (Or.inl h'')) h2⟩
        have hsub : ({x, y, z} : Finset W) ⊆ L \ New := fun w hw =>
          Finset.mem_sdiff.mpr ⟨hTL hw, hTN w hw⟩
        rw [hset, Finset.card_sdiff_of_subset hsub, hT3,
          Finset.card_insert_of_notMem hxN] at hcount
        have := Finset.card_le_card hsub
        omega
      · obtain ⟨𝒳₁, hfol₁, hw₁⟩ := hlift 𝒳' hfol'
        obtain ⟨𝒳, hfol, hw⟩ := ep_fol_tri_lift α β L x y z exy eyz ezx h ht hTcut 𝒳₁ hfol₁
        exact ⟨𝒳, hfol, hw₁.trans hw⟩

open Classical in
/-- **Corollary 4 with weights.** A foliage of weight `w` gives at least
`2 ^ (w / (3 β₁))` perfect matchings. -/
theorem ep_fol0_count {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (hc : EpCubic α β L) (hb : EpBridgeless α β L) (𝒳 : Finset (Finset W))
    (hfol : EpFol0 α β L 𝒳) :
    (2 : ℝ) ^ (epFw α β 𝒳 * (995 / 196) / 3) ≤ (epM α β L : ℝ) := by
  have hle : epFw α β 𝒳 ≤ (𝒳.card : ℝ) * (196 / 995) := by
    unfold epFw
    calc _ ≤ ∑ _X ∈ 𝒳, (196 : ℝ) / 995 :=
          Finset.sum_le_sum (fun X _ => by split_ifs <;> norm_num)
      _ = (𝒳.card : ℝ) * (196 / 995) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hinj : ∀ i j : Fin 𝒳.card, i ≠ j → (𝒳.equivFin.symm i).1 ≠ (𝒳.equivFin.symm j).1 :=
    fun i j hij h' => hij (𝒳.equivFin.symm.injective (Subtype.ext h'))
  have hcount := ep_foliage_count α β L hc hb (fun i : Fin 𝒳.card => (𝒳.equivFin.symm i).1)
    (fun i => (hfol.1 _ (𝒳.equivFin.symm i).2).1)
    (fun i j hij => hfol.2 _ (𝒳.equivFin.symm i).2 _ (𝒳.equivFin.symm j).2 (hinj i j hij))
    (fun i => (hfol.1 _ (𝒳.equivFin.symm i).2).2)
  refine le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_) hcount
  have : epFw α β 𝒳 * (995 / 196) ≤ (𝒳.card : ℝ) := by
    have := mul_le_mul_of_nonneg_right hle (by norm_num : (0 : ℝ) ≤ 995 / 196)
    calc epFw α β 𝒳 * (995 / 196) ≤ (𝒳.card : ℝ) * (196 / 995) * (995 / 196) := this
      _ = (𝒳.card : ℝ) := by ring
  linarith

set_option maxHeartbeats 1600000 in
open Classical in
/-- **Theorem 1 for connected multigraphs.** A cubic bridgeless connected multigraph on `|L|`
vertices has at least `2 ^ (|L| / 4749)` perfect matchings. -/
theorem lp_multigraph_bound {W E : Type*} [Fintype E] (α β : E → W) (L : Finset W)
    (hc : EpCubic α β L) (hb : EpBridgeless α β L) (hconn : EpConnected α β L) :
    (2 : ℝ) ^ ((1 / 4749 : ℝ) * L.card) ≤ (epM α β L : ℝ) := by
  have h := hc.toD
  by_cases hL0 : L = ∅
  · subst hL0
    have : (∅ : Finset E) ∈ epPMs α β (∅ : Finset W) := by
      rw [mem_epPMs]
      exact ⟨fun e he => absurd he (Finset.notMem_empty e),
        fun c hc' => absurd hc' (Finset.notMem_empty c)⟩
    have h1 : 1 ≤ epM α β (∅ : Finset W) := Finset.card_pos.mpr ⟨∅, this⟩
    rw [Finset.card_empty]
    simp only [Nat.cast_zero, mul_zero, Real.rpow_zero]
    exact_mod_cast h1
  · obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hL0
    obtain ⟨g₀, hg₀⟩ := Finset.card_pos.mp (by rw [h.2 v hv]; norm_num : 0 < (epCut α β {v}).card)
    have hg₀L : α g₀ ∈ L := (hc.1 g₀).1
    have hMe : ∀ g, epMe α β L g ≤ epM α β L := fun g => Finset.card_filter_le _ _
    by_cases hsmall : L.card ≤ 4749
    · obtain ⟨M₁, M₂, hM₁, hM₂, hne, -, -⟩ := epD_two_pm_avoiding α β L h hb g₀ hg₀L
      have h2 : 2 ≤ epM α β L := by
        have : ({M₁, M₂} : Finset (Finset E)) ⊆ epPMs α β L := by
          intro M hM
          rcases Finset.mem_insert.mp hM with rfl | hM
          · exact (mem_epPMs _ _ _ _).mpr hM₁
          · rw [Finset.mem_singleton.mp hM]; exact (mem_epPMs _ _ _ _).mpr hM₂
        have := Finset.card_le_card this
        rw [Finset.card_pair hne] at this
        exact this
      have h1 : (2 : ℝ) ^ ((1 / 4749 : ℝ) * L.card) ≤ (2 : ℝ) ^ (1 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have : (L.card : ℝ) ≤ 4749 := by exact_mod_cast hsmall
        linarith
      rw [Real.rpow_one] at h1
      have : (2 : ℝ) ≤ (epM α β L : ℝ) := by exact_mod_cast h2
      linarith
    · push_neg at hsmall
      obtain ⟨α', β', L', hreach, hpr, hcount, hlift⟩ := ep_prune_full L.card α β L ∅ rfl h hb hconn
        (Finset.empty_subset _)
        (fun _ _ _ _ _ _ _ => ⟨Finset.notMem_empty _, Finset.notMem_empty _, Finset.notMem_empty _⟩)
      rw [Finset.card_empty, Finset.sdiff_empty] at hcount
      obtain ⟨h', hb', hconn', -⟩ := hreach.preserves h hb hconn
      have hL3 : (L.card : ℝ) ≤ 3 * (L'.card : ℝ) := by exact_mod_cast (by omega : L.card ≤ 3 * L'.card)
      -- a heavy foliage of the pruned multigraph suffices
      have hheavy : ∀ 𝒳', EpFol0 α' β' L' 𝒳' →
          (L.card : ℝ) * (1 / 2985 - 1 / 4749) ≤ epFw α' β' 𝒳' →
          (2 : ℝ) ^ ((1 / 4749 : ℝ) * L.card) ≤ (epM α β L : ℝ) := by
        intro 𝒳' hfol' hw'
        obtain ⟨𝒳, hfol, hw⟩ := hlift 𝒳' hfol'
        refine le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
          (ep_fol0_count α β L hc hb 𝒳 hfol)
        have : (L.card : ℝ) * (1 / 2985 - 1 / 4749) ≤ epFw α β 𝒳 := hw'.trans hw
        nlinarith
      by_cases hcore : EpHasCore α' β' L'
      · obtain ⟨𝒳₀, hfol₀, hmax₀⟩ := ep_fw_max α' β' L'
        by_cases hF : (L.card : ℝ) * (1 / 2985 - 1 / 4749) ≤ epFw α' β' 𝒳₀
        · exact hheavy 𝒳₀ hfol₀ hF
        · push_neg at hF
          have h13 := ep_lemma13 L'.card α' β' L' rfl h' hb' hconn' hpr hcore _ hmax₀
          have hk : ∀ g, α' g ∈ L' → ⌈(2 : ℝ) ^ ((1 / 4749 : ℝ) * L.card)⌉₊ ≤ epMe α' β' L' g := by
            intro g hg
            apply Nat.ceil_le.mpr
            refine le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_) (h13 g hg)
            nlinarith
          have hfin := EpReach.mstar_le hreach h hb hconn _ hk g₀ hg₀L
          calc (2 : ℝ) ^ ((1 / 4749 : ℝ) * L.card)
              ≤ (⌈(2 : ℝ) ^ ((1 / 4749 : ℝ) * L.card)⌉₊ : ℝ) := Nat.le_ceil _
            _ ≤ (epM α β L : ℝ) := by exact_mod_cast hfin.trans (hMe g₀)
      · obtain ⟨v', hv'⟩ : L'.Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨𝒳', hfol', hw'⟩ := ep_cor12 α' β' L' v' h' hb' hconn' hv' hcore hpr (by omega)
        refine hheavy 𝒳' hfol'.toFol0 ?_
        nlinarith

/--
**The Lovász–Plummer conjecture (1970s), proved by Esperet, Kardoš, King, Král' and Norine
(2011).**

Every bridgeless cubic graph on $n$ vertices has exponentially many perfect matchings: there is
a constant $c > 0$ such that the number of perfect matchings is at least $2^{cn}$.
[EKKKN11] prove this with $2^{n/3656}$.
-/
@[category research solved, AMS 5]
theorem lovasz_plummer_conjecture :
    ∃ c : ℝ, 0 < c ∧ ∀ {V : Type} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      (∀ v, G.degree v = 3) → G.IsBridgeless →
      (2 : ℝ) ^ (c * Fintype.card V) ≤ perfectMatchingCount G := by
  refine ⟨1 / 4749, by norm_num, fun {V} _ _ G _ hcubic hbr => ?_⟩
  exact lp_of_multigraph (1 / 4749)
    (fun W E _ α β L hc hb => lp_reduce_connected (1 / 4749)
      (fun W E _ α β L hc hb hconn => lp_multigraph_bound α β L hc hb hconn)
      L.card W E α β L rfl hc hb)
    G hcubic hbr

/--
**The explicit bound of Esperet–Kardoš–King–Král'–Norine (2011).**

Every bridgeless cubic graph on $n$ vertices has at least $2^{n/3656}$ perfect matchings.

*Reference:* [EKKKN11].
-/
@[category research solved, AMS 5]
theorem lovasz_plummer_conjecture.variants.explicit
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless) :
    (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G := by
  sorry

/-- A **Hamiltonian cycle** of `G`: a cycle passing through every vertex. -/
def IsHamiltonianCycle (G : SimpleGraph V) {v : V} (c : G.Walk v v) : Prop :=
  c.IsCycle ∧ ∀ w, w ∈ c.support

/--
**Sheehan's conjecture (1977).**

Every $4$-regular graph with a Hamiltonian cycle has a second Hamiltonian cycle (one with a
different edge set). Sheehan's conjecture would settle the last open case of the question,
raised by Smith's theorem for cubic graphs, of which regular Hamiltonian graphs have a second
Hamiltonian cycle: Thomassen [Th98] proved it for all $r$-regular graphs with $r \ge 300$.
-/
@[category research open, AMS 5]
theorem sheehan_conjecture :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (∀ v, G.degree v = 4) →
      ∀ (v : V) (c : G.Walk v v), IsHamiltonianCycle G c →
        ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
          c'.edges.toFinset ≠ c.edges.toFinset := by
  sorry

/--
**Thomassen (1998): regular graphs of large degree.**

Every $r$-regular Hamiltonian graph with $r \ge 300$ has a second Hamiltonian cycle.

*Reference:* [Th98].
-/
@[category research solved, AMS 5]
theorem sheehan_conjecture.variants.thomassen
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r)
    (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c) :
    ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset := by
  sorry

end LovaszPlummerConjecture
