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
# Erdős Problem 156

*References:*
- [erdosproblems.com/156](https://www.erdosproblems.com/156)
- [ESS94] Erdős, P. and Sárközy, A. and Sós, T., On Sum Sets of Sidon Sets, I. Journal of Number
  Theory (1994), 329-347.
- [Ru98b] Ruzsa, Imre Z., A small maximal Sidon set. Ramanujan J. (1998), 55-58.
-/

@[expose] public section

open Finset Filter

namespace Erdos156

/--
The size of the smallest maximal Sidon set in $\{1, \dots, N\}$.
-/
noncomputable def minMaximalSidonSet (N : ℕ) : ℕ :=
  open scoped Classical in
  sInf (((Icc 1 N).powerset.filter fun (A : Finset ℕ) ↦
    Set.IsMaximalSidonSetIn (A : Set ℕ) N).image card : Set ℕ)

/--
Does there exist a maximal Sidon set $A\subset \{1,\ldots,N\}$ of size $O(N^{1/3})$?

A question of Erdős, Sárközy, and Sós [ESS94].
-/
@[category research open, AMS 5]
theorem erdos_156 :
    answer(sorry) ↔
      (fun N ↦ (minMaximalSidonSet N : ℝ)) =O[atTop] (fun N ↦ (N : ℝ) ^ (1 / 3 : ℝ)) := by
  sorry

@[category test, AMS 5]
theorem greedySidonSet_isSidon (n : ℕ) : IsSidon (Finset.greedySidonBelow n : Set ℕ) := by
  intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ eq
  have subset : Finset.greedySidonBelow n ⊆ (Finset.greedySidon.aux n).1 := Finset.filter_subset _ _
  exact (Finset.greedySidon.aux n).1.2 i₁ (subset hi₁) j₁ (subset hj₁) i₂ (subset hi₂) j₂ (subset hj₂) eq

open Finset in
lemma gs_go_min (A : Finset ℕ) (hA : IsSidon (A : Set ℕ)) (m x : ℕ) (h : A.Nonempty)
    (hmx : m ≤ x) (hx : x < (greedySidon.go A hA m).1) :
    ¬ (x ∉ A ∧ IsSidon ((A ∪ {x} : Finset ℕ) : Set ℕ)) := by
  intro hc
  rw [greedySidon.go, dif_pos h] at hx
  exact Nat.find_min _ hx ⟨hmx, hc⟩


open Finset in
lemma gs_aux_succ_fst (k : ℕ) :
    (greedySidon.aux (k + 1)).1.1 = (greedySidon.aux k).1.1 ∪ {(greedySidon.aux (k + 1)).2} := by
  rw [greedySidon.aux.eq_def (k + 1)]

open Finset in
lemma gs_aux_succ_snd (k : ℕ) (h : ((greedySidon.aux k).1.1).Nonempty) :
    (greedySidon.aux (k + 1)).2 = (greedySidon.go (greedySidon.aux k).1.1 (greedySidon.aux k).1.2
          (((greedySidon.aux k).1.1).max' h + 1)).1 := by
  rw [greedySidon.aux.eq_def (k + 1)]
  have e : (if h : ((greedySidon.aux k).1.1).Nonempty then ((greedySidon.aux k).1.1).max' h + 1
      else (greedySidon.aux k).2) = ((greedySidon.aux k).1.1).max' h + 1 := dif_pos h
  exact congrArg (fun m => (greedySidon.go _ (greedySidon.aux k).1.2 m).1) e


lemma gs_nonsidon {C : Finset ℕ} (hC : IsSidon (C : Set ℕ)) {x : ℕ}
    (h : ¬ IsSidon ((C ∪ {x} : Finset ℕ) : Set ℕ)) :
    ∃ a ∈ C, ∃ b ∈ C, ∃ c ∈ C, x + a = b + c ∨ x + x = b + c := by
  simp only [IsSidon, Finset.coe_union, Finset.coe_singleton, Set.mem_union, Finset.mem_coe,
    Set.mem_singleton_iff] at h
  push Not at h
  obtain ⟨i1, hi1, j1, hj1, i2, hi2, j2, hj2, heq, hn1, hn2⟩ := h
  rcases hi1 with hi1 | rfl <;> rcases hj1 with hj1 | rfl <;> rcases hi2 with hi2 | rfl <;>
    rcases hj2 with hj2 | rfl
  · exact absurd (hC _ hi1 _ hj1 _ hi2 _ hj2 heq) (by tauto)
  · exact ⟨j1, hj1, i1, hi1, i2, hi2, Or.inl (by omega)⟩
  · exact ⟨i1, hi1, j1, hj1, j2, hj2, Or.inl (by omega)⟩
  · omega
  · exact ⟨j2, hj2, i1, hi1, i2, hi2, Or.inl (by omega)⟩
  · exact ⟨i1, hi1, i1, hi1, i2, hi2, Or.inr (by omega)⟩
  · omega
  · omega
  · exact ⟨i2, hi2, j1, hj1, j2, hj2, Or.inl (by omega)⟩
  · omega
  · exact ⟨j1, hj1, j1, hj1, j2, hj2, Or.inr (by omega)⟩
  · omega
  · omega
  · omega
  · omega
  · omega

abbrev gsA (k : ℕ) : Finset ℕ := (Finset.greedySidon.aux k).1.1
abbrev gsS (k : ℕ) : ℕ := (Finset.greedySidon.aux k).2

open Finset in
lemma gs_inv (k : ℕ) : (gsA k).Nonempty ∧ gsS k ∈ gsA k ∧ (∀ a ∈ gsA k, a ≤ gsS k) ∧
    k + 1 ≤ gsS k := by
  induction k with
  | zero =>
    have h0 : greedySidon.aux 0 = (⟨{1}, by simp [IsSidon]⟩, 1) := by
      rw [greedySidon.aux.eq_def]
    simp [gsA, gsS, h0]
  | succ k ih =>
    obtain ⟨hne, hmem, hle, hk⟩ := ih
    have hmax : (gsA k).max' hne = gsS k := le_antisymm (max'_le _ _ _ hle) (le_max' _ _ hmem)
    have hs := gs_aux_succ_snd k hne
    have hA := gs_aux_succ_fst k
    have hge : gsS k + 1 ≤ gsS (k + 1) := by
      have := (greedySidon.go (greedySidon.aux k).1.1 (greedySidon.aux k).1.2
          (((greedySidon.aux k).1.1).max' hne + 1)).2.1
      simp only [gsS, gsA] at hmax ⊢
      rw [hs, ← hmax]; exact this
    refine ⟨?_, ?_, ?_, by omega⟩
    · simp only [gsA] at hA ⊢; rw [hA]; simp
    · simp only [gsA, gsS] at hA ⊢; rw [hA]; simp
    · intro a ha
      simp only [gsA, gsS] at hA ha hle ⊢
      rw [hA, mem_union, mem_singleton] at ha
      rcases ha with ha | ha
      · have := hle a ha; simp only [gsS] at hge; omega
      · omega

open Finset in
lemma gs_mono (k : ℕ) : gsA k ⊆ gsA (k + 1) := by
  have hA := gs_aux_succ_fst k
  simp only [gsA] at hA ⊢
  rw [hA]; exact subset_union_left

lemma gs_mono' {k N : ℕ} (h : k ≤ N) : gsA k ⊆ gsA N := by
  induction N with
  | zero => obtain rfl : k = 0 := by omega
            exact le_rfl
  | succ N ih =>
    rcases Nat.lt_or_ge k (N + 1) with h' | h'
    · exact (ih (by omega)).trans (gs_mono N)
    · obtain rfl : k = N + 1 := by omega
      exact le_rfl

open Finset in
lemma gs_skip {k x : ℕ} (h1 : gsS k < x) (h2 : x < gsS (k + 1)) :
    ¬ IsSidon ((gsA k ∪ {x} : Finset ℕ) : Set ℕ) := by
  obtain ⟨hne, hmem, hle, -⟩ := gs_inv k
  have hmax : (gsA k).max' hne = gsS k := le_antisymm (max'_le _ _ _ hle) (le_max' _ _ hmem)
  have hs := gs_aux_succ_snd k hne
  intro hS
  refine gs_go_min (greedySidon.aux k).1.1 (greedySidon.aux k).1.2 ((gsA k).max' hne + 1) x hne ?_ ?_ ⟨?_, hS⟩
  · simp only [gsA, gsS] at hmax h1 ⊢; omega
  · simp only [gsS] at h2; rw [← hs]; exact h2
  · intro hx; have := hle x hx; omega

lemma gs_cover (N : ℕ) : ∀ x, 1 ≤ x → x ≤ gsS N →
    x ∈ gsA N ∨ ∃ k < N, gsS k < x ∧ x < gsS (k + 1) := by
  induction N with
  | zero =>
    intro x hx1 hx2
    obtain ⟨-, hmem, -, -⟩ := gs_inv 0
    have h0 : gsS 0 = 1 := by
      simp only [gsS]; rw [Finset.greedySidon.aux.eq_def]
    left; rw [show x = 1 by omega, ← h0]; exact hmem
  | succ N ih =>
    intro x hx1 hx2
    rcases Nat.lt_or_ge (gsS N) x with h | h
    · rcases Nat.lt_or_ge x (gsS (N + 1)) with h' | h'
      · exact Or.inr ⟨N, by omega, h, h'⟩
      · left; rw [show x = gsS (N + 1) by omega]; exact (gs_inv (N + 1)).2.1
    · rcases ih x hx1 h with h3 | ⟨k, hk, h4⟩
      · exact Or.inl (gs_mono N h3)
      · exact Or.inr ⟨k, by omega, h4⟩

open Finset in
lemma gs_card_bound (N : ℕ) : N ≤ 3 * (greedySidonBelow N).card ^ 3 := by
  set B := greedySidonBelow N with hB
  have hBdef : B = (gsA N).filter (· ≤ N) := rfl
  set T := (B ×ˢ B ×ˢ B).image (fun p : ℕ × ℕ × ℕ => p.2.1 + p.2.2 - p.1) ∪
    (B ×ˢ B).image (fun p : ℕ × ℕ => (p.1 + p.2) / 2) with hT
  have hsub : Icc 1 N ⊆ B ∪ T := by
    intro x hx
    rw [mem_Icc] at hx
    have hN := (gs_inv N).2.2.2
    rcases gs_cover N x hx.1 (by omega) with h | ⟨k, hk, h1, h2⟩
    · exact mem_union_left _ (by rw [hBdef, mem_filter]; exact ⟨h, hx.2⟩)
    · apply mem_union_right
      obtain ⟨a, ha, b, hb, c, hc, he⟩ := gs_nonsidon (greedySidon.aux k).1.2 (gs_skip h1 h2)
      have hleK := (gs_inv k).2.2.1
      have inB : ∀ y ∈ gsA k, y ∈ B := by
        intro y hy
        rw [hBdef, mem_filter]
        exact ⟨gs_mono' hk.le hy, by have := hleK y hy; omega⟩
      rcases he with he | he
      · exact mem_union_left _ (mem_image.mpr ⟨(a, b, c), by simp [inB a ha, inB b hb, inB c hc], by simp; omega⟩)
      · exact mem_union_right _ (mem_image.mpr ⟨(b, c), by simp [inB b hb, inB c hc], by simp; omega⟩)
  have hcard := card_le_card hsub
  simp only [Nat.card_Icc, add_tsub_cancel_right] at hcard
  have hT' : T.card ≤ B.card ^ 3 + B.card ^ 2 := by
    refine (card_union_le _ _).trans (add_le_add ?_ ?_)
    · refine card_image_le.trans ?_; simp [card_product]; ring_nf; rfl
    · refine card_image_le.trans ?_; simp [card_product]; ring_nf; rfl
  have hu := card_union_le B T
  have b1 : B.card ≤ B.card ^ 3 := by
    rcases Nat.eq_zero_or_pos B.card with h | h
    · simp [h]
    · exact Nat.le_self_pow (by norm_num) _
  have b2 : B.card ^ 2 ≤ B.card ^ 3 := by
    rcases Nat.eq_zero_or_pos B.card with h | h
    · simp [h]
    · exact Nat.pow_le_pow_right h (by norm_num)
  omega

/--
It is easy to prove that the greedy construction of a maximal Sidon set in $\{1,\ldots,N\}$ has size
$\gg N^{1/3}$.
-/
@[category research solved, AMS 5]
theorem erdos_156.variants.greedy_lower_bound :
    (fun N ↦ ((Finset.greedySidonBelow N).card : ℝ)) ≫ (fun N ↦ (N : ℝ) ^ (1 / 3 : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound 2 (Filter.Eventually.of_forall fun N => ?_)
  set b := (Finset.greedySidonBelow N).card
  have hb : (N : ℝ) ≤ (2 * (b : ℝ)) ^ 3 := by
    have h := gs_card_bound N
    have h' : (N : ℝ) ≤ 3 * (b : ℝ) ^ 3 := by exact_mod_cast h
    have : (0 : ℝ) ≤ (b : ℝ) ^ 3 := by positivity
    nlinarith
  have h0 : (0 : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) := by positivity
  rw [Real.norm_of_nonneg h0, Real.norm_of_nonneg (by positivity)]
  calc (N : ℝ) ^ (1 / 3 : ℝ) ≤ ((2 * (b : ℝ)) ^ 3) ^ (1 / 3 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hb (by norm_num)
    _ = 2 * b := by
        rw [show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
        exact Real.pow_rpow_inv_natCast (by positivity) (by norm_num)

/--
Ruzsa [Ru98b] constructed a maximal Sidon set of size $\ll (N\log N)^{1/3}$.
-/
@[category research solved, AMS 5]
theorem erdos_156.variants.ruzsa_upper_bound :
    (fun N ↦ (minMaximalSidonSet N : ℝ)) ≪
      (fun N ↦ ((N : ℝ) * Real.log N) ^ (1 / 3 : ℝ)) := by
  sorry

end Erdos156
