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
# Erdős Problem 120

*Reference:*
- [erdosproblems.com/120](https://www.erdosproblems.com/120)
- [St20](http://matwbn.icm.edu.pl/ksiazki/fm/fm1/fm1111.pdf) Steinhaus, Hugo, Sur les distances des points dans les ensembles de measure positive. Fund. Math. (1920), 93-104.
-/

@[expose] public section

open Set MeasureTheory

namespace Erdos120

/--
There exists a set $E \subseteq \mathbb{R}$, dependent on set $A \subseteq \mathbb{R}$,
of positive measure which does not contain any set of the shape $a * A + b$
for some $a,b \in \mathbb{R}$ and $a \neq 0$?
-/
def Erdos120For (A : Set ℝ) : Prop := ∃ E : Set ℝ,
  MeasurableSet E ∧ 0 < volume E ∧ ∀ a b : ℝ, a ≠ 0 → ¬ .image (fun x => a * x + b) A ⊆ E

/--
Let $A \subseteq \mathbb{R}$ be an infinite set. Must there be a set $E \subseteq \mathbb{R}$
of positive measure which does not contain any set of the shape $a * A + b$
for some $a,b \in \mathbb{R}$ and $a \neq 0$?
-/
@[category research open, AMS 5 28]
theorem erdos_120 : answer(sorry) ↔ ∀ A : Set ℝ, A.Infinite → Erdos120For A := by
  sorry

open MeasureTheory Filter Topology in
/-- Shifted interval excess. -/
lemma e120_shift (c r s : ℝ) (hr : 0 < r) :
    volume (Set.Icc (c - r) (c + r) ∩ (fun b => b + s) ⁻¹' (Set.Icc (c - r) (c + r))ᶜ) ≤
      ENNReal.ofReal |s| := by
  rcases le_total 0 s with hs | hs
  · calc _ ≤ volume (Set.Icc (c + r - s) (c + r)) := by
          apply measure_mono
          rintro b ⟨⟨hb1, hb2⟩, hb3⟩
          simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hb3
          constructor
          · rcases hb3 with h | h <;> linarith
          · exact hb2
      _ = ENNReal.ofReal |s| := by rw [Real.volume_Icc, abs_of_nonneg hs]; ring_nf
  · calc _ ≤ volume (Set.Icc (c - r) (c - r - s)) := by
          apply measure_mono
          rintro b ⟨⟨hb1, hb2⟩, hb3⟩
          simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hb3
          constructor
          · exact hb1
          · rcases hb3 with h | h <;> linarith
      _ = ENNReal.ofReal |s| := by rw [Real.volume_Icc, abs_of_nonpos hs]; ring_nf

open MeasureTheory Filter Topology in
/-- The bad set for one shift. -/
lemma e120_bad (E : Set ℝ) (hE : MeasurableSet E) (c r s : ℝ) (hr : 0 < r) :
    volume (Set.Icc (c - r) (c + r) ∩ (fun b => b + s) ⁻¹' Eᶜ) ≤
      ENNReal.ofReal |s| + volume (Set.Icc (c - r) (c + r) \ E) := by
  set B := Set.Icc (c - r) (c + r)
  have hsub : B ∩ (fun b => b + s) ⁻¹' Eᶜ ⊆
      (B ∩ (fun b => b + s) ⁻¹' Bᶜ) ∪ ((fun b => b + s) ⁻¹' (B \ E)) := by
    rintro b ⟨hbB, hbE⟩
    by_cases h : b + s ∈ B
    · exact Or.inr ⟨h, hbE⟩
    · exact Or.inl ⟨hbB, h⟩
  calc _ ≤ volume ((B ∩ (fun b => b + s) ⁻¹' Bᶜ) ∪ ((fun b => b + s) ⁻¹' (B \ E))) := measure_mono hsub
    _ ≤ volume (B ∩ (fun b => b + s) ⁻¹' Bᶜ) + volume ((fun b => b + s) ⁻¹' (B \ E)) := measure_union_le _ _
    _ ≤ ENNReal.ofReal |s| + volume (B \ E) :=
        add_le_add (e120_shift c r s hr) (le_of_eq (measure_preimage_add_right _ _ _))

open MeasureTheory Filter Topology in
/-- A density point gives an interval almost filled by `E`. -/
lemma e120_dense (E : Set ℝ) (hE : MeasurableSet E) (hpos : 0 < volume E) (ε : ℝ) (hε : 0 < ε) :
    ∃ x r : ℝ, 0 < r ∧ volume (Set.Icc (x - r) (x + r) \ E) ≤ ENNReal.ofReal (ε * (2 * r)) := by
  have hae := Besicovitch.ae_tendsto_measure_inter_div (volume : Measure ℝ) E
  haveI : (ae (volume.restrict E)).NeBot := by
    rw [ae_neBot, Ne, Measure.restrict_eq_zero]; exact hpos.ne'
  obtain ⟨x, hx⟩ := hae.exists
  have hlt : (1 : ENNReal) - ENNReal.ofReal ε < 1 :=
    ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero (by simpa using hε)
  have hev := (tendsto_order.1 hx).1 _ hlt
  obtain ⟨r, hr, hrpos⟩ := (hev.and self_mem_nhdsWithin).exists
  have hrpos' : 0 < r := hrpos
  refine ⟨x, r, hrpos', ?_⟩
  rw [← Real.closedBall_eq_Icc]
  set B := Metric.closedBall x r
  have hB : volume B = ENNReal.ofReal (2 * r) := by
    rw [Real.volume_closedBall]
  have hB0 : volume B ≠ 0 := by rw [hB]; simp [hrpos']
  have hBt : volume B ≠ ⊤ := by rw [hB]; exact ENNReal.ofReal_ne_top
  rw [ENNReal.lt_div_iff_mul_lt (Or.inl hB0) (Or.inl hBt)] at hr
  have hdiff : B \ E = B \ (E ∩ B) := by
    ext y; simp only [Set.mem_diff, Set.mem_inter_iff]; tauto
  rw [hdiff, measure_diff_le_iff_le_add (hE.inter measurableSet_closedBall).nullMeasurableSet
    Set.inter_subset_right (measure_ne_top_of_subset Set.inter_subset_right hBt)]
  have h1 : volume B ≤ (1 - ENNReal.ofReal ε) * volume B + ENNReal.ofReal ε * volume B := by
    rw [← add_mul]
    calc volume B = 1 * volume B := (one_mul _).symm
      _ ≤ (1 - ENNReal.ofReal ε + ENNReal.ofReal ε) * volume B := by gcongr; exact le_tsub_add
  calc volume B ≤ (1 - ENNReal.ofReal ε) * volume B + ENNReal.ofReal ε * volume B := h1
    _ ≤ volume (E ∩ B) + ENNReal.ofReal (ε * (2 * r)) := by
        gcongr
        rw [hB, ENNReal.ofReal_mul hε.le]

open MeasureTheory Filter Topology in
theorem e120_main {A : Set ℝ} (h : A.Finite) : ¬ Erdos120For A := by
  classical
  rintro ⟨E, hE, hpos, hno⟩
  set S := h.toFinset with hSdef
  rcases Nat.eq_zero_or_pos S.card with hk0 | hkpos
  · have hA : A = ∅ := by
      rw [← h.coe_toFinset, ← hSdef, Finset.card_eq_zero.mp hk0, Finset.coe_empty]
    exact hno 1 0 one_ne_zero (by simp [hA])
  set k := S.card
  have hk : (0 : ℝ) < k := by exact_mod_cast hkpos
  set M : ℝ := 1 + ∑ a ∈ S, |a|
  have hM1 : 1 ≤ M := by
    have := Finset.sum_nonneg (fun a (_ : a ∈ S) => abs_nonneg a); linarith
  have hMa : ∀ a ∈ S, |a| ≤ M := fun a ha => by
    have := Finset.single_le_sum (fun a (_ : a ∈ S) => abs_nonneg a) ha; linarith
  obtain ⟨x, r, hr, hdens⟩ := e120_dense E hE hpos (1 / (4 * k)) (by positivity)
  set t := r / (4 * k * M)
  have ht : 0 < t := by positivity
  set B := Set.Icc (x - r) (x + r)
  have hbad : ∀ a ∈ S, volume (B ∩ (fun b => b + t * a) ⁻¹' Eᶜ) ≤
      ENNReal.ofReal (3 * r / (4 * k)) := by
    intro a ha
    refine (e120_bad E hE x r (t * a) hr).trans ?_
    have h1 : |t * a| ≤ r / (4 * k) := by
      rw [abs_mul, abs_of_pos ht]
      calc t * |a| ≤ t * M := mul_le_mul_of_nonneg_left (hMa a ha) ht.le
        _ = r / (4 * k) := by simp only [t]; field_simp
    calc ENNReal.ofReal |t * a| + volume (B \ E)
        ≤ ENNReal.ofReal (r / (4 * k)) + ENNReal.ofReal (1 / (4 * k) * (2 * r)) :=
          add_le_add (ENNReal.ofReal_le_ofReal h1) hdens
      _ = ENNReal.ofReal (3 * r / (4 * k)) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; field_simp; ring
  have hunion : volume (⋃ a ∈ S, B ∩ (fun b => b + t * a) ⁻¹' Eᶜ) < volume B := by
    calc _ ≤ ∑ a ∈ S, volume (B ∩ (fun b => b + t * a) ⁻¹' Eᶜ) := measure_biUnion_finset_le _ _
      _ ≤ ∑ _a ∈ S, ENNReal.ofReal (3 * r / (4 * k)) := Finset.sum_le_sum hbad
      _ = ENNReal.ofReal (3 * r / 4) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1; field_simp; rfl
      _ < volume B := by
          rw [Real.volume_Icc]
          exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
  obtain ⟨b, hbB, hbnot⟩ : ∃ b ∈ B, b ∉ ⋃ a ∈ S, B ∩ (fun b => b + t * a) ⁻¹' Eᶜ := by
    by_contra hcon
    push Not at hcon
    exact absurd (measure_mono (fun y hy => hcon y hy)) (not_le.mpr hunion)
  apply hno t b ht.ne'
  rintro _ ⟨a, ha, rfl⟩
  simp only [Set.mem_iUnion, not_exists] at hbnot
  by_contra hE'
  refine hbnot a (h.mem_toFinset.mpr ha) ⟨hbB, ?_⟩
  simp only [Set.mem_preimage, Set.mem_compl_iff]
  rwa [add_comm]

/--
Steinhaus [St20] has proved Erdős 120 to be false whenever $A$ is a finite set.
-/
@[category research solved, AMS 5 28]
theorem erdos_120.variants.finite_set {A : Set ℝ} (h : A.Finite) : ¬ Erdos120For A := by
  exact e120_main h

end Erdos120
