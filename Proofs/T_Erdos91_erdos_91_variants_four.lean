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


/--
For $n = 3$ the equilateral triangle is the only such set.
-/
@[category research solved, AMS 52]
theorem erdos_91.variants.three : UniqueMinimizer 3 := by
  sorry


lemma e91_dist (a b c d : ℝ) : dist (!₂[a, b]) (!₂[c, d]) = Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp [Real.dist_eq, sq_abs]

/-- No four points in the plane are pairwise equidistant (Gram determinant argument). -/
lemma e91_no_equi4 (a1 a2 b1 b2 c1 c2 d1 d2 D : ℝ) (hD : 0 < D)
    (hab : (b1 - a1) ^ 2 + (b2 - a2) ^ 2 = D) (hac : (c1 - a1) ^ 2 + (c2 - a2) ^ 2 = D)
    (had : (d1 - a1) ^ 2 + (d2 - a2) ^ 2 = D) (hbc : (c1 - b1) ^ 2 + (c2 - b2) ^ 2 = D)
    (hbd : (d1 - b1) ^ 2 + (d2 - b2) ^ 2 = D) (hcd : (d1 - c1) ^ 2 + (d2 - c2) ^ 2 = D) : False := by
  set u1 := b1 - a1; set u2 := b2 - a2
  set v1 := c1 - a1; set v2 := c2 - a2
  set w1 := d1 - a1; set w2 := d2 - a2
  have huv : u1 * v1 + u2 * v2 = D / 2 := by
    have : (c1 - b1) = v1 - u1 := by ring
    have : (c2 - b2) = v2 - u2 := by ring
    nlinarith
  have huw : u1 * w1 + u2 * w2 = D / 2 := by
    have : (d1 - b1) = w1 - u1 := by ring
    have : (d2 - b2) = w2 - u2 := by ring
    nlinarith
  have hvw : v1 * w1 + v2 * w2 = D / 2 := by
    have : (d1 - c1) = w1 - v1 := by ring
    have : (d2 - c2) = w2 - v2 := by ring
    nlinarith
  have key : (u1 ^ 2 + u2 ^ 2) * (v1 ^ 2 + v2 ^ 2) * (w1 ^ 2 + w2 ^ 2)
      + 2 * (u1 * v1 + u2 * v2) * (v1 * w1 + v2 * w2) * (u1 * w1 + u2 * w2)
      - (u1 ^ 2 + u2 ^ 2) * (v1 * w1 + v2 * w2) ^ 2 - (v1 ^ 2 + v2 ^ 2) * (u1 * w1 + u2 * w2) ^ 2
      - (w1 ^ 2 + w2 ^ 2) * (u1 * v1 + u2 * v2) ^ 2 = 0 := by ring
  rw [hab, hac, had, huv, huw, hvw] at key
  nlinarith [pow_pos hD 3]

lemma e91_dist_sq (x y : EuclideanSpace ℝ (Fin 2)) :
    dist x y ^ 2 = (y 0 - x 0) ^ 2 + (y 1 - x 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two, Real.dist_eq,
    Real.dist_eq, sq_abs, sq_abs]
  ring

/-- Every 4-point set in the plane has at least 2 distinct distances. -/
lemma e91_two_le (A : Finset (EuclideanSpace ℝ (Fin 2))) (hA : A.card = 4) :
    2 ≤ distinctDistances A := by
  classical
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ := Finset.card_eq_four.mp hA
  unfold distinctDistances distanceSet
  by_contra hlt
  push Not at hlt
  have hmem : ∀ x ∈ ({a, b, c, d} : Finset _), ∀ y ∈ ({a, b, c, d} : Finset _), x ≠ y →
      dist x y = dist a b := by
    intro x hx y hy hxy
    have h1 : dist x y ∈ (({a, b, c, d} : Finset _).offDiag.image fun p => dist p.1 p.2) :=
      Finset.mem_image.mpr ⟨(x, y), Finset.mem_offDiag.mpr ⟨hx, hy, hxy⟩, rfl⟩
    have h2 : dist a b ∈ (({a, b, c, d} : Finset _).offDiag.image fun p => dist p.1 p.2) :=
      Finset.mem_image.mpr ⟨(a, b), Finset.mem_offDiag.mpr ⟨by simp, by simp, hab⟩, rfl⟩
    exact Finset.card_le_one.mp (by omega) _ h1 _ h2
  have hD : 0 < dist a b ^ 2 := by have := dist_pos.mpr hab; positivity
  have e := fun x y (hx : x ∈ ({a, b, c, d} : Finset _)) (hy : y ∈ ({a, b, c, d} : Finset _))
    (hxy : x ≠ y) => (e91_dist_sq x y).symm.trans (by rw [hmem x hx y hy hxy])
  exact e91_no_equi4 (a 0) (a 1) (b 0) (b 1) (c 0) (c 1) (d 0) (d 1) (dist a b ^ 2) hD
    (e a b (by simp) (by simp) hab) (e a c (by simp) (by simp) hac) (e a d (by simp) (by simp) had)
    (e b c (by simp) (by simp) hbc) (e b d (by simp) (by simp) hbd) (e c d (by simp) (by simp) hcd)





/-- Two equilateral triangles sharing an edge. -/
noncomputable def e91Rhombus : Finset ℝ² :=
  {!₂[0, 0], !₂[1, 0], !₂[1 / 2, Real.sqrt 3 / 2], !₂[1 / 2, -(Real.sqrt 3 / 2)]}

lemma e91_sq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

lemma e91_square_dist : ∀ x ∈ unitSquare, ∀ y ∈ unitSquare, x ≠ y →
    dist x y = 1 ∨ dist x y = Real.sqrt 2 := by
  intro x hx y hy hxy
  simp only [unitSquare, Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    first | exact absurd rfl hxy | (rw [e91_dist]; norm_num)

lemma e91_rh_dist : ∀ x ∈ e91Rhombus, ∀ y ∈ e91Rhombus, x ≠ y →
    dist x y = 1 ∨ dist x y = Real.sqrt 3 := by
  intro x hx y hy hxy
  simp only [e91Rhombus, Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    first | exact absurd rfl hxy | (rw [e91_dist]; ring_nf; (try rw [e91_sq3]); norm_num)

lemma e91_ne {a b c d : ℝ} (h : a ≠ c ∨ b ≠ d) : (!₂[a, b] : ℝ²) ≠ !₂[c, d] := by
  intro e
  have h0 := congrArg (fun v : ℝ² => v 0) e
  have h1 := congrArg (fun v : ℝ² => v 1) e
  simp at h0 h1
  tauto

lemma e91_sqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)

lemma e91_square_card : unitSquare.card = 4 := by
  classical
  unfold unitSquare
  rw [Finset.card_eq_four]
  refine ⟨_, _, _, _, e91_ne ?_, e91_ne ?_, e91_ne ?_, e91_ne ?_, e91_ne ?_, e91_ne ?_, rfl⟩ <;> norm_num

lemma e91_rh_card : e91Rhombus.card = 4 := by
  classical
  unfold e91Rhombus
  rw [Finset.card_eq_four]
  have := e91_sqrt3_pos
  refine ⟨_, _, _, _, e91_ne ?_, e91_ne ?_, e91_ne ?_, e91_ne ?_, e91_ne ?_, e91_ne ?_, rfl⟩
  all_goals first | (right; intro h; linarith) | (left; norm_num)

lemma e91_dd_le_two (A : Finset ℝ²) (u v : ℝ)
    (hd : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → dist x y = u ∨ dist x y = v) : distinctDistances A ≤ 2 := by
  classical
  unfold distinctDistances distanceSet
  calc (A.offDiag.image fun p => dist p.1 p.2).card ≤ ({u, v} : Finset ℝ).card := by
        apply Finset.card_le_card
        intro z hz
        obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨hx, hy, hne⟩ := Finset.mem_offDiag.mp hxy
        rcases hd x hx y hy hne with h | h <;> simp [h]
    _ ≤ 2 := Finset.card_le_two

lemma e91_min4 : minimalDistinctDistances ℝ² 4 = 2 := by
  have hsq : distinctDistances unitSquare = 2 :=
    le_antisymm (e91_dd_le_two _ _ _ e91_square_dist) (e91_two_le _ e91_square_card)
  apply le_antisymm
  · exact Nat.sInf_le ⟨unitSquare, e91_square_card, hsq⟩
  · exact le_csInf ⟨2, unitSquare, e91_square_card, hsq⟩
      (fun m ⟨pts, hc, hm⟩ => hm ▸ e91_two_le pts hc)

lemma e91_opt (A : Finset ℝ²) (hc : A.card = 4) (u v : ℝ)
    (hd : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → dist x y = u ∨ dist x y = v) : IsOptimal A 4 :=
  ⟨hc, by rw [e91_min4]; exact le_antisymm (e91_dd_le_two A u v hd) (e91_two_le A hc)⟩

lemma e91_not_similar : ¬ DilationEquivSimilar unitSquare e91Rhombus := by
  rintro ⟨f, hf⟩
  set r : ℝ := (Dilation.ratio f : ℝ)
  have hr : 0 < r := by have := Dilation.ratio_pos f; exact_mod_cast this
  -- preimages of two rhombus pairs
  have pre : ∀ z ∈ e91Rhombus, ∃ x ∈ unitSquare, f x = z := by
    intro z hz
    have : z ∈ f '' (unitSquare : Set ℝ²) := by rw [hf]; exact hz
    obtain ⟨x, hx, rfl⟩ := this
    exact ⟨x, hx, rfl⟩
  have scaled : ∀ z₁ ∈ e91Rhombus, ∀ z₂ ∈ e91Rhombus, z₁ ≠ z₂ →
      dist z₁ z₂ = r * 1 ∨ dist z₁ z₂ = r * Real.sqrt 2 := by
    intro z₁ h₁ z₂ h₂ hne
    obtain ⟨x, hx, rfl⟩ := pre z₁ h₁
    obtain ⟨y, hy, rfl⟩ := pre z₂ h₂
    have hxy : x ≠ y := fun h => hne (h ▸ rfl)
    rw [Dilation.dist_eq]
    rcases e91_square_dist x hx y hy hxy with h | h <;> simp [h, r]
  have m1 : (!₂[0, 0] : ℝ²) ∈ e91Rhombus := by simp [e91Rhombus]
  have m2 : (!₂[1, 0] : ℝ²) ∈ e91Rhombus := by simp [e91Rhombus]
  have m3 : (!₂[1 / 2, Real.sqrt 3 / 2] : ℝ²) ∈ e91Rhombus := by simp [e91Rhombus]
  have m4 : (!₂[1 / 2, -(Real.sqrt 3 / 2)] : ℝ²) ∈ e91Rhombus := by simp [e91Rhombus]
  have s3 := e91_sqrt3_pos
  have d12 : dist (!₂[0, 0] : ℝ²) (!₂[1, 0]) = 1 := by rw [e91_dist]; norm_num
  have d34 : dist (!₂[1 / 2, Real.sqrt 3 / 2] : ℝ²) (!₂[1 / 2, -(Real.sqrt 3 / 2)]) =
      Real.sqrt 3 := by rw [e91_dist]; ring_nf; rw [e91_sq3]; try norm_num
  have h1 := scaled _ m1 _ m2 (e91_ne (by norm_num))
  have h2 := scaled _ m3 _ m4 (e91_ne (by right; intro h; linarith))
  rw [d12] at h1
  rw [d34] at h2
  have q2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have q3 := e91_sq3
  have p2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> (try simp only [mul_one] at h1 h2)
  · nlinarith
  · have : Real.sqrt 3 ^ 2 = r ^ 2 * Real.sqrt 2 ^ 2 := by rw [h2]; ring
    nlinarith
  · have e1 : (r * Real.sqrt 2) ^ 2 = 1 := by rw [← h1]; norm_num
    have e2 : r ^ 2 = 3 := by rw [← h2]; exact q3
    have : (r * Real.sqrt 2) ^ 2 = r ^ 2 * Real.sqrt 2 ^ 2 := by ring
    nlinarith
  · nlinarith

/--
For $n=4$ the square or two equilateral triangles sharing an edge give two
non-similar examples.
-/
@[category research solved, AMS 52]
theorem erdos_91.variants.four : ¬ UniqueMinimizer 4 :=
fun h =>
  e91_not_similar (h unitSquare e91Rhombus
    (e91_opt _ e91_square_card 1 (Real.sqrt 2) e91_square_dist)
    (e91_opt _ e91_rh_card 1 (Real.sqrt 3) e91_rh_dist))


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
