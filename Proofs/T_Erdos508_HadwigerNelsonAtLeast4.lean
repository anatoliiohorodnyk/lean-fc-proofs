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
# Erdős Problem 508

*Reference:* [erdosproblems.com/508](https://www.erdosproblems.com/508)

proven by considering the [Moser-Spindel graph]
or the [Golomb graph]
*At least 4 colors are required:* [Moser-Spindel graph](https://de.wikipedia.org/wiki/Moser-Spindel)
*At least 4 colors are required:* [Golomb graph](https://en.wikipedia.org/wiki/Golomb_graph)
*At least 5 colors are required:* [de Grey 2018](https://arxiv.org/abs/1804.02385)
-/

@[expose] public section

open SimpleGraph
open scoped EuclideanGeometry

namespace Erdos508

scoped notation "χ(ℝ²)" => SimpleGraph.chromaticNumber (UnitDistancePlaneGraph Set.univ)

/--
The Hadwiger–Nelson problem asks: How many colors are required to color the plane
such that no two points at distance 1 from each other have the same color?
-/
@[category research open, AMS 52]
theorem HadwigerNelsonProblem :
    χ(ℝ²) = answer(sorry) := by
  sorry

/--
Aubrey de Grey improved the lower bound for the chromatic number of the plane
to 5 in 2018 using a graph that has >1000 nodes.

"The chromatic number of the plane is at least 5" Aubrey D. N. J. de Grey, 2018
(https://doi.org/10.48550/arXiv.1804.02385)
-/
@[category research solved, AMS 52]
theorem HadwigerNelsonAtLeastFive :
    5 ≤ χ(ℝ²) := by
  sorry

noncomputable def moserPt (x y : ℝ) : (Set.univ : Set (EuclideanSpace ℝ (Fin 2))) :=
  ⟨!₂[x, y], Set.mem_univ _⟩

lemma moser_adj {x₁ y₁ x₂ y₂ : ℝ} (h : (x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2 = 1) :
    (UnitDistancePlaneGraph Set.univ).Adj (moserPt x₁ y₁) (moserPt x₂ y₂) := by
  change dist (moserPt x₁ y₁) (moserPt x₂ y₂) = 1
  simp only [moserPt, Subtype.dist_eq, EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp [Real.dist_eq, sq_abs, h]

lemma fin3_eq {a b c d : Fin 3} (h1 : a ≠ b) (h2 : a ≠ c) (h3 : b ≠ c) (h4 : d ≠ b) (h5 : d ≠ c) :
    a = d := by omega

/-- In a proper 3-colouring, the two tips of a unit rhombus get the same colour. -/
lemma moser_rhombus (C : (UnitDistancePlaneGraph Set.univ).Coloring (Fin 3))
    {a b c d : (Set.univ : Set (EuclideanSpace ℝ (Fin 2)))}
    (hab : (UnitDistancePlaneGraph Set.univ).Adj a b) (hac : (UnitDistancePlaneGraph Set.univ).Adj a c)
    (hbc : (UnitDistancePlaneGraph Set.univ).Adj b c) (hdb : (UnitDistancePlaneGraph Set.univ).Adj d b)
    (hdc : (UnitDistancePlaneGraph Set.univ).Adj d c) : C a = C d :=
  fin3_eq (C.valid hab) (C.valid hac) (C.valid hbc) (C.valid hdb) (C.valid hdc)

/--
The "chromatic number of the plane" is at least 4. This can be
proven by considering the [Moser-Spindel graph](https://de.wikipedia.org/wiki/Moser-Spindel)
or the [Golomb graph](https://en.wikipedia.org/wiki/Golomb_graph) graph.
-/
@[category research solved, AMS 5]
theorem HadwigerNelsonAtLeast4 : 4 ≤ χ(ℝ²) := by
  by_contra hlt
  push Not at hlt
  have h3 : (UnitDistancePlaneGraph Set.univ).chromaticNumber ≤ (3 : ℕ) := Order.le_of_lt_add_one hlt
  obtain ⟨C⟩ := chromaticNumber_le_iff_colorable.mp h3
  have s3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have s11 : Real.sqrt 11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  set r := Real.sqrt 3
  set t := Real.sqrt 11
  -- first rhombus: (0,0), (√3/2, ±1/2), (√3, 0)
  have e1 : C (moserPt 0 0) = C (moserPt r 0) :=
    moser_rhombus C (b := moserPt (r/2) (1/2)) (c := moserPt (r/2) (-1/2))
      (moser_adj (by nlinarith)) (moser_adj (by nlinarith)) (moser_adj (by nlinarith))
      (moser_adj (by nlinarith)) (moser_adj (by nlinarith))
  -- second rhombus: (0,0) to (5√3/6, √33/6) = (5r/6, r t/6)
  have e2 : C (moserPt 0 0) = C (moserPt (5*r/6) (r*t/6)) :=
    moser_rhombus C (b := moserPt (5*r/12 - t/12) (r*t/12 + 5/12))
      (c := moserPt (5*r/12 + t/12) (r*t/12 - 5/12))
      (moser_adj (by ring_nf; simp only [s3, s11]; ring_nf)) (moser_adj (by ring_nf; simp only [s3, s11]; ring_nf))
      (moser_adj (by ring_nf; simp only [s3, s11]; ring_nf))
      (moser_adj (by ring_nf; simp only [s3, s11]; ring_nf)) (moser_adj (by ring_nf; simp only [s3, s11]; ring_nf))
  have hadj : (UnitDistancePlaneGraph Set.univ).Adj (moserPt r 0) (moserPt (5*r/6) (r*t/6)) :=
    moser_adj (by ring_nf; simp only [s3, s11]; ring_nf)
  exact C.valid hadj (e1.symm.trans e2)

/--
This upper bound for the chromatic number of the plane was
observed by John R. Isbell. His approach was dividing the
plane into hexagons of uniform size and coloring them with a repeating
pattern. A proof can probably be found in:

Soifer, Alexander (2008), The Mathematical Coloring Book: Mathematics of Coloring and the Colorful Life of its Creators, New York: Springer, ISBN 978-0-387-74640-1

An alternative approach that uses square tiling was highlighted by László Székely.
-/
@[category textbook, AMS 52]
theorem HadwigerNelsonAtMostSeven :
    χ(ℝ²) ≤ 7 := by
  sorry

/-- The chromatic number of the plane is at least 3.

This is proven by considering an equilateral triangle in the plane. -/
@[category textbook, AMS 5]
theorem HadwigerNelsonAtLeastThree : 3 ≤ χ(ℝ²) :=
  le_chromaticNumber_of_pairwise_adj (by simp)
    ![(⟨!₂[0, 0], Set.mem_univ _⟩ : ↥(Set.univ : Set (EuclideanSpace ℝ (Fin 2)))),
      (⟨!₂[1, 0], Set.mem_univ _⟩ : ↥(Set.univ : Set (EuclideanSpace ℝ (Fin 2)))),
      (⟨!₂[0.5, Real.sqrt 3 / 2], Set.mem_univ _⟩ : ↥(Set.univ : Set (EuclideanSpace ℝ (Fin 2))))] <| by
    simp [pairwise_fin_succ_iff_of_isSymm, Fin.forall_fin_succ]
    simp [UnitDistancePlaneGraph, PiLp.dist_eq_of_L2, Real.dist_eq, div_pow, Subtype.dist_eq]
    norm_num
