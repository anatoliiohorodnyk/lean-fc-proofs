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
# Erdős Problem 91

*Reference:*
- [Er87b] Erdős, P., Some combinatorial and metric problems in geometry.
  Intuitive geometry (Siófok, 1985) (1987), 167-177.
- [Ko24c] Z. Kovács, A note on Erdős's mysterious remark. arXiv:2412.05190 (2024).
- [erdosproblems.com/91](https://www.erdosproblems.com/91)
-/

@[expose] public section

open Finset EuclideanGeometry Filter

namespace Erdos91

/-- A set $A$ is 'optimal' if it has $n$ points and achieves the minimum distance count. -/
noncomputable def IsOptimal (A : Finset ℝ²) (n : ℕ) : Prop :=
  A.card = n ∧ distinctDistances A = minimalDistinctDistances ℝ² n

/-- Two finite sets of points in $\mathbb{R}^2$ are similar if one can be mapped to the other by a
DilationEquiv. -/
def DilationEquivSimilar (A B : Finset ℝ²) : Prop :=
  ∃ f : ℝ² ≃ᵈ ℝ², (f '' A) = B

/-- Equilateral triangle with unit side length, resting on the x-axis with one vertex at the origin. -/
noncomputable def equiTriangle : Finset ℝ² := {!₂[0, 0], !₂[1, 0], !₂[1 / 2, Real.sqrt 3 / 2]}

noncomputable def unitSquare : Finset ℝ² := {!₂[0, 0], !₂[0, 1], !₂[1, 0], !₂[1, 1]}

/-- Regular 7-gon with unit side length, touching both axes in the first quadrant. -/
noncomputable def circleSeven : Finset ℝ² :=
  let r := 1 / (2 * Real.sin (Real.pi / 7))
  let cx := r * Real.cos (Real.pi / 7)
  let cy := r * Real.sin (4 * Real.pi / 7)
  (Finset.range 7).image fun k : ℕ =>
    !₂[r * Real.cos (2 * Real.pi * ↑k / 7) + cx, r * Real.sin (2 * Real.pi * ↑k / 7) + cy]

/-- Wheel graph on 7 vertices (center + regular hexagon) with unit side length,
touching both axes in the first quadrant. -/
noncomputable def wheelSeven : Finset ℝ² :=
  {!₂[1, Real.sqrt 3 / 2],
   !₂[2, Real.sqrt 3 / 2],
   !₂[3 / 2, Real.sqrt 3],
   !₂[1 / 2, Real.sqrt 3],
   !₂[0, Real.sqrt 3 / 2],
   !₂[1 / 2, 0],
   !₂[3 / 2, 0]}

@[category test, AMS 52]
lemma erdos_91.test.equiTriangle_optimal : IsOptimal equiTriangle 3 := by
  have hcard : equiTriangle.card = 3 := by
    simp [equiTriangle, Finset.mem_insert, Finset.mem_singleton]
  have hdist : distinctDistances equiTriangle = 1 := by
    unfold distinctDistances distanceSet equiTriangle
    have eucl_dist_one_of_sq : ∀ {x y : ℝ²}, dist x y ^ 2 = 1 → dist x y = 1 := by
      intro x y h; nlinarith [dist_nonneg (x := x) (y := y), sq_nonneg (dist x y)]
    have hd01 : dist (!₂[(0 : ℝ), 0]) (!₂[(1 : ℝ), 0]) = 1 := eucl_dist_one_of_sq <| by
      rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]; simp [Real.dist_eq]
    have hd02 : dist (!₂[(0 : ℝ), 0]) (!₂[(1 : ℝ) / 2, Real.sqrt 3 / 2]) = 1 :=
      eucl_dist_one_of_sq <| by
        rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        nlinarith [Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num), Real.sqrt_nonneg 3,
          sq_abs ((0 : ℝ) - 1 / 2), sq_abs ((0 : ℝ) - Real.sqrt 3 / 2)]
    have hd12 : dist (!₂[(1 : ℝ), 0]) (!₂[(1 : ℝ) / 2, Real.sqrt 3 / 2]) = 1 :=
      eucl_dist_one_of_sq <| by
        rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        nlinarith [Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num), Real.sqrt_nonneg 3,
          sq_abs ((1 : ℝ) - 1 / 2), sq_abs ((0 : ℝ) - Real.sqrt 3 / 2)]
    suffices h : ({!₂[(0 : ℝ), 0], !₂[(1 : ℝ), 0], !₂[(1 : ℝ) / 2, Real.sqrt 3 / 2]} :
        Finset ℝ²).offDiag.image (fun (pair : ℝ² × ℝ²) => dist pair.1 pair.2) = {1} by
      simp only [h, Finset.card_singleton]
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_image.mpr
      ⟨⟨!₂[0, 0], !₂[1, 0]⟩, by simp [Finset.mem_offDiag], hd01⟩, fun d hd => ?_⟩
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hd
    simp only [Finset.mem_offDiag, Finset.mem_insert, Finset.mem_singleton] at hab
    obtain ⟨ha, hb, _⟩ := hab
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> first
      | contradiction | exact hd01 | exact hd02 | exact hd12
      | (rw [dist_comm]; first | exact hd01 | exact hd02 | exact hd12)
  have hmin : minimalDistinctDistances ℝ² 3 = 1 := by
    unfold minimalDistinctDistances
    apply le_antisymm
    · exact Nat.sInf_le ⟨equiTriangle, hcard, by exact_mod_cast hdist⟩
    · apply le_csInf
      · exact ⟨_, equiTriangle, hcard, rfl⟩
      rintro d ⟨points, hcard', hd⟩
      rw [← show distinctDistances points = d from by exact_mod_cast hd]
      exact Finset.card_pos.mpr ((Finset.card_pos.mp (by rw [Finset.offDiag_card, hcard']; norm_num :
        0 < points.offDiag.card)).image _)
  exact ⟨hcard, by rw [hdist, hmin]⟩

@[category test, AMS 52]
lemma erdos_91.test.equiTriangle_unique_optimal :
    ∀ A : Finset ℝ², IsOptimal A 3 → DilationEquivSimilar A equiTriangle := by
  sorry

@[category test, AMS 52]
lemma erdos_91.test.unitSquare_optimal : IsOptimal unitSquare 4 := by
  sorry

@[category test, AMS 52]
lemma erdos_91.test.circleSeven_optimal : IsOptimal circleSeven 7 := by
  sorry

@[category test, AMS 52]
lemma erdos_91.test.wheelSeven_optimal : IsOptimal wheelSeven 7 := by
  sorry

@[category test, AMS 52]
lemma erdos_91.test.dissimilar_circleSeven_wheelSeven :
    ¬DilationEquivSimilar circleSeven wheelSeven := by
  sorry

/--
The predicate on $n$ asserting all $A, B\subset \mathbb{R}^2$,
with $\lvert A\rvert=n = \lvert B\rvert$, which minimise the number of distinct points for all sets
with $n$ elements are similar.
-/
def UniqueMinimizer (n : ℕ) : Prop :=
  ∀ A B : Finset ℝ², IsOptimal A n → IsOptimal B n → DilationEquivSimilar A B

/--
Suppose $A\subset \mathbb{R}^2$ has $\lvert A\rvert=n$ and minimises the number of distinct
distances between points in $A$. Prove that for large $n$ there are at least two
(and probably many) such $A$ which are non-similar.
-/
@[category research open, AMS 52]
theorem erdos_91 :
    answer(sorry) ↔ ∀ᶠ n : ℕ in atTop, ¬ UniqueMinimizer n := by
  sorry


lemma e91t_norm_comb (u v : ℝ²) (α β : ℝ) :
    ‖α • u + β • v‖ ^ 2 = α ^ 2 * ‖u‖ ^ 2 + 2 * α * β * inner ℝ u v + β ^ 2 * ‖v‖ ^ 2 := by
  rw [norm_add_sq_real, norm_smul, norm_smul, inner_smul_left, inner_smul_right]
  simp only [Real.norm_eq_abs, mul_pow, sq_abs, conj_trivial]
  ring

/-- Equilateral data: `‖u‖ = ‖v‖ = s`, `⟪u, v⟫ = s²/2`. -/
lemma e91t_inner {u v : ℝ²} {s : ℝ} (hu : ‖u‖ = s) (hv : ‖v‖ = s) (huv : ‖u - v‖ = s) :
    inner ℝ u v = s ^ 2 / 2 := by
  have := norm_sub_sq_real u v
  rw [hu, hv, huv] at this
  linarith

lemma e91t_li {u v : ℝ²} {s : ℝ} (hs : 0 < s) (hu : ‖u‖ = s) (hv : ‖v‖ = s)
    (huv : ‖u - v‖ = s) : LinearIndependent ℝ ![u, v] := by
  rw [LinearIndependent.pair_iff]
  intro α β h
  have hn := e91t_norm_comb u v α β
  rw [h, norm_zero, hu, hv, e91t_inner hu hv huv] at hn
  have hs2 : 0 < s ^ 2 := by positivity
  have : α ^ 2 + α * β + β ^ 2 = 0 := by
    have : s ^ 2 * (α ^ 2 + α * β + β ^ 2) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact h
  constructor <;> nlinarith [sq_nonneg (α + β), sq_nonneg α, sq_nonneg β]

lemma e91t_sim (a b c a' b' c' : ℝ²) (s s' : ℝ) (hs : 0 < s) (hs' : 0 < s')
    (hab : dist a b = s) (hac : dist a c = s) (hbc : dist b c = s)
    (hab' : dist a' b' = s') (hac' : dist a' c' = s') (hbc' : dist b' c' = s') :
    ∃ f : ℝ² ≃ᵈ ℝ², f a = a' ∧ f b = b' ∧ f c = c' := by
  have prep : ∀ (a b c : ℝ²) (s : ℝ), dist a b = s → dist a c = s → dist b c = s →
      ‖b - a‖ = s ∧ ‖c - a‖ = s ∧ ‖(b - a) - (c - a)‖ = s := by
    intro a b c s h1 h2 h3
    refine ⟨?_, ?_, ?_⟩
    · rw [← dist_eq_norm, dist_comm, h1]
    · rw [← dist_eq_norm, dist_comm, h2]
    · rw [sub_sub_sub_cancel_right, ← dist_eq_norm, h3]
  obtain ⟨hu, hv, huv⟩ := prep a b c s hab hac hbc
  obtain ⟨hu', hv', huv'⟩ := prep a' b' c' s' hab' hac' hbc'
  have hfin : Fintype.card (Fin 2) = Module.finrank ℝ ℝ² := by simp
  let bu := basisOfLinearIndependentOfCardEqFinrank (e91t_li hs hu hv huv) hfin
  let bu' := basisOfLinearIndependentOfCardEqFinrank (e91t_li hs' hu' hv' huv') hfin
  let L : ℝ² ≃ₗ[ℝ] ℝ² := bu.equiv bu' (Equiv.refl (Fin 2))
  have hL0 : L (b - a) = b' - a' := by
    have := bu.equiv_apply 0 bu' (Equiv.refl (Fin 2))
    simpa [bu, bu', coe_basisOfLinearIndependentOfCardEqFinrank] using this
  have hL1 : L (c - a) = c' - a' := by
    have := bu.equiv_apply 1 bu' (Equiv.refl (Fin 2))
    simpa [bu, bu', coe_basisOfLinearIndependentOfCardEqFinrank] using this
  have hnorm : ∀ x, ‖L x‖ = (s' / s) * ‖x‖ := by
    intro x
    have hx : x = bu.repr x 0 • (b - a) + bu.repr x 1 • (c - a) := by
      conv_lhs => rw [← bu.sum_repr x]
      simp [Fin.sum_univ_two, bu, coe_basisOfLinearIndependentOfCardEqFinrank]
    set α := bu.repr x 0
    set β := bu.repr x 1
    have hLx : L x = α • (b' - a') + β • (c' - a') := by
      rw [hx, map_add, map_smul, map_smul, hL0, hL1]
    have h1 := e91t_norm_comb (b - a) (c - a) α β
    have h2 := e91t_norm_comb (b' - a') (c' - a') α β
    rw [hu, hv, e91t_inner hu hv huv] at h1
    rw [hu', hv', e91t_inner hu' hv' huv'] at h2
    rw [← hx] at h1
    rw [← hLx] at h2
    have h3 : ‖L x‖ ^ 2 = ((s' / s) * ‖x‖) ^ 2 := by
      rw [h2, mul_pow, h1, div_pow]; field_simp
    exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h3
  let r : NNReal := ⟨s' / s, by positivity⟩
  let e : ℝ² ≃ ℝ² :=
    { toFun := fun x => a' + L (x - a)
      invFun := fun y => a + L.symm (y - a')
      left_inv := fun x => by simp
      right_inv := fun y => by simp }
  let f : ℝ² ≃ᵈ ℝ² :=
    { toEquiv := e
      edist_eq' := ⟨r, (show 0 < r from NNReal.coe_pos.mp (show (0 : ℝ) < s' / s by positivity)).ne',
        fun x y => by
        simp only [e, edist_dist, dist_eq_norm]
        rw [add_sub_add_left_eq_sub, ← map_sub, sub_sub_sub_cancel_right, hnorm,
          ENNReal.ofReal_mul (by positivity)]
        congr 1
        show ENNReal.ofReal ((r : NNReal) : ℝ) = r
        exact ENNReal.ofReal_coe_nnreal⟩ }
  refine ⟨f, ?_, ?_, ?_⟩
  · show a' + L (a - a) = a'
    simp
  · show a' + L (b - a) = b'
    rw [hL0]; abel
  · show a' + L (c - a) = c'
    rw [hL1]; abel

lemma e91_dist (a b c d : ℝ) : dist (!₂[a, b]) (!₂[c, d]) = Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp [Real.dist_eq, sq_abs]





lemma e91t_equi_dd : distinctDistances equiTriangle ≤ 1 := by
  classical
  unfold distinctDistances distanceSet
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  calc _ ≤ ({1} : Finset ℝ).card := by
        apply Finset.card_le_card
        intro z hz
        obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨hx, hy, hne⟩ := Finset.mem_offDiag.mp hxy
        simp only [equiTriangle, Finset.mem_insert, Finset.mem_singleton] at hx hy
        rw [Finset.mem_singleton]
        rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
          first | exact absurd rfl hne | (rw [e91_dist]; ring_nf; (try rw [h3]); try norm_num)
    _ = 1 := rfl

/-- An optimal 3-set is an equilateral triangle. -/
lemma e91t_equilateral (A : Finset ℝ²) (hA : IsOptimal A 3) (hE : equiTriangle.card = 3) :
    ∃ a b c, A = {a, b, c} ∧ 0 < dist a b ∧ dist a c = dist a b ∧ dist b c = dist a b := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hA.1
  have hle : distinctDistances ({a, b, c} : Finset ℝ²) ≤ 1 := by
    rw [hA.2]
    unfold minimalDistinctDistances
    exact (Nat.sInf_le (show distinctDistances equiTriangle ∈
      {m | ∃ points : Finset ℝ², points.card = 3 ∧ distinctDistances points = m} from
        ⟨equiTriangle, hE, rfl⟩)).trans e91t_equi_dd
  unfold distinctDistances distanceSet at hle
  have key : ∀ x ∈ ({a, b, c} : Finset ℝ²), ∀ y ∈ ({a, b, c} : Finset ℝ²), x ≠ y →
      dist x y = dist a b := by
    intro x hx y hy hxy
    exact Finset.card_le_one.mp hle _
      (Finset.mem_image.mpr ⟨(x, y), Finset.mem_offDiag.mpr ⟨hx, hy, hxy⟩, rfl⟩) _
      (Finset.mem_image.mpr ⟨(a, b), Finset.mem_offDiag.mpr ⟨by simp, by simp, hab⟩, rfl⟩)
  exact ⟨a, b, c, rfl, dist_pos.mpr hab, key a (by simp) c (by simp) hac,
    key b (by simp) c (by simp) hbc⟩

/--
For $n = 3$ the equilateral triangle is the only such set.
-/
@[category research solved, AMS 52]
theorem erdos_91.variants.three : UniqueMinimizer 3 := by
  have hE : equiTriangle.card = 3 := erdos_91.test.equiTriangle_optimal.1
  intro A B hA hB
  obtain ⟨a, b, c, rfl, hs, h2, h3⟩ := e91t_equilateral A hA hE
  obtain ⟨a', b', c', rfl, hs', h2', h3'⟩ := e91t_equilateral B hB hE
  obtain ⟨f, fa, fb, fc⟩ := e91t_sim a b c a' b' c' _ _ hs hs' rfl h2 h3 rfl h2' h3'
  refine ⟨f, ?_⟩
  simp [Set.image_insert_eq, fa, fb, fc]


/--
For $n=4$ the square or two equilateral triangles sharing an edge give two
non-similar examples.
-/
@[category research solved, AMS 52]
theorem erdos_91.variants.four : ¬ UniqueMinimizer 4 := by
  sorry


/--
For $n = 5$ the regular pentagon is the unique such set (which has two distinct distances).
Erdős mysteriously remarks in [Er90] this was proved by 'a colleague'. (In [Er87b] this is
described as 'a colleague from Zagreb (unfortunately I do not have his letter)'.)
A published proof of this fact is provided by Kovács [Ko24c].
-/
@[category research solved, AMS 52]
theorem erdos_91.variants.five : UniqueMinimizer 5 := by
  sorry

/--
In [Er87b] on p.171 Erdős says that there are at least two non-similar examples for $n = 6$.
-/
@[category research solved, AMS 52]
theorem erdos_91.variants.six: ¬ UniqueMinimizer 6 := by
  sorry


/--
In [Er87b] on p.171 Erdős says that there are at least two non-similar examples for $n = 7$.
-/
@[category research solved, AMS 52]
theorem erdos_91.variants.seven: ¬ UniqueMinimizer 7 := by
  sorry


/--
In [Er87b] on p.171 Erdős says that there are at least two non-similar examples for $n = 8$.
-/
@[category research solved, AMS 52]
theorem erdos_91.variants.eight: ¬ UniqueMinimizer 8 := by
  sorry


/--
In [Er87b] on p.171 Erdős says that there are at least two non-similar examples for $n = 9$.
-/
@[category research solved, AMS 52]
theorem erdos_91.variants.nine: ¬ UniqueMinimizer 9 := by
  sorry

end Erdos91
