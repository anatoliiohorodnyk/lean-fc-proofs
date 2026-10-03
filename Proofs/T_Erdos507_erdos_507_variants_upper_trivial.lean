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
# Erdős Problem 507

*References:*
- [erdosproblems.com/507](https://www.erdosproblems.com/507)
- [CPZ23] Cohen, Alex, Cosmin Pohoata, and Dmitrii Zakharov. "A new upper bound for the Heilbronn
  triangle problem." arXiv preprint arXiv:2305.18253 (2023).
- [CPZ24] Cohen, Alex, Cosmin Pohoata, and Dmitrii Zakharov. "Lower bounds for incidences."
  Inventiones mathematicae (2025): 1-74.
- [KPS82] Komlós, János, János Pintz, and Endre Szemerédi. "A lower bound for Heilbronn's problem."
  Journal of the London Mathematical Society 2.1 (1982): 13-24.
- [KPS81] Komlós, János, János Pintz, and Endre Szemerédi. "On Heilbronn's triangle problem."
  Journal of the London Mathematical Society 2.3 (1981): 385-396.
-/

@[expose] public section

open Asymptotics Filter Topology
open scoped EuclideanGeometry

namespace Erdos507

/--
The minimum (unsigned) area of a triangle determined by three distinct points in a set `S`.
Collinear triples count with area `0`. `EuclideanGeometry.triangle_area` is a signed area, so the
absolute value is taken before the infimum.
-/
noncomputable def minTriangleArea (S : Finset ℝ²) : ℝ :=
  sInf {abs (EuclideanGeometry.triangle_area (p 0) (p 1) (p 2)) |
    (p : Fin 3 → ℝ²) (_ : Function.Injective p) (_ : ∀ i, p i ∈ S)}

/--
$\alpha(n)$ is the supremum of `minTriangleArea S` over all sets `S` of $n$ points in the unit disk.
-/
noncomputable def α (n : ℕ) : ℝ :=
  sSup (minTriangleArea '' { S : Finset ℝ² |
    S.card = n ∧ ↑S ⊆ Metric.closedBall (0 : ℝ²) 1 ∧ ¬ Collinear ℝ (S : Set ℝ²) })

/--
Current best lower bound [KPS82].
-/
noncomputable def lowerBest (n : ℕ) : ℝ := Real.log n / (n : ℝ) ^ 2

/--
The "Barrier" function: n^(-7/6) used for the best upper bound [CPZ24].
-/
noncomputable def upperBarrier (n : ℕ) : ℝ := 1 / (n : ℝ) ^ ((7 : ℝ) / 6)

/--
Let $\alpha(n)$ be such that every set of $n$ points in the unit disk contains three points which
determine a triangle of area at most $\alpha(n)$. Estimate $\alpha(n)$.
-/
@[category research open, AMS 51]
theorem erdos_507.equivalent:
    α ~[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

/--
Estimate a lower bound for$\alpha(n)$.
-/
@[category research open, AMS 51]
theorem erdos_507.lower:
    let ans := (answer(sorry) : ℕ → ℝ)
    (lowerBest =o[atTop] ans) ∧ (ans ≪ α) := by
  sorry

/--
Estimate an upper bound for$\alpha(n)$.
-/
@[category research open, AMS 51]
theorem erdos_507.upper:
    let ans := (answer(sorry) : ℕ → ℝ)
    (α ≪ ans) ∧ (ans =o[atTop] upperBarrier) := by
  sorry

lemma e507u_coord_le (x : ℝ²) (i : Fin 2) : |x i| ≤ ‖x‖ := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  apply Real.le_sqrt_of_sq_le
  simp only [Real.norm_eq_abs, sq_abs]
  change x i ^ 2 ≤ x 0 ^ 2 + x 1 ^ 2
  fin_cases i <;> simp <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]

lemma e507u_area (a b c : ℝ²) (δ : ℝ) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1)
    (hac : |a 0 - c 0| ≤ δ) (hbc : |b 0 - c 0| ≤ δ) :
    |EuclideanGeometry.triangle_area a b c| ≤ 2 * δ := by
  rw [EuclideanGeometry.triangle_area_eq_det, Matrix.det_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
    Matrix.tail_cons]
  simp only [Matrix.vecHead, Matrix.vecTail, mul_one]
  have a1 := (e507u_coord_le a 1).trans ha
  have b1 := (e507u_coord_le b 1).trans hb
  have c1 := (e507u_coord_le c 1).trans hc
  have hb1c1 : |b 1 - c 1| ≤ 2 := by
    calc |b 1 - c 1| ≤ |b 1| + |c 1| := abs_sub _ _
      _ ≤ 2 := by linarith
  have ha1c1 : |a 1 - c 1| ≤ 2 := by
    calc |a 1 - c 1| ≤ |a 1| + |c 1| := abs_sub _ _
      _ ≤ 2 := by linarith
  have hδ : 0 ≤ δ := le_trans (abs_nonneg _) hac
  have key : a.ofLp 0 * b.ofLp 1 - a.ofLp 0 * c.ofLp 1 - b.ofLp 0 * a.ofLp 1 + b.ofLp 0 * c.ofLp 1 +
      c.ofLp 0 * a.ofLp 1 - c.ofLp 0 * b.ofLp 1 =
      (a 0 - c 0) * (b 1 - c 1) - (b 0 - c 0) * (a 1 - c 1) := by
    change _ = (a.ofLp 0 - c.ofLp 0) * (b.ofLp 1 - c.ofLp 1) - (b.ofLp 0 - c.ofLp 0) * (a.ofLp 1 - c.ofLp 1)
    ring
  rw [key, abs_div, abs_two]
  have h1 : |(a 0 - c 0) * (b 1 - c 1)| ≤ δ * 2 := by
    rw [abs_mul]; exact mul_le_mul hac hb1c1 (abs_nonneg _) hδ
  have h2 : |(b 0 - c 0) * (a 1 - c 1)| ≤ δ * 2 := by
    rw [abs_mul]; exact mul_le_mul hbc ha1c1 (abs_nonneg _) hδ
  have h3 := abs_sub ((a 0 - c 0) * (b 1 - c 1)) ((b 0 - c 0) * (a 1 - c 1))
  rw [div_le_iff₀ (by norm_num)]
  linarith

lemma e507u_bucket (B : ℕ) (hB : 1 ≤ B) (p : ℝ²) (hp : ‖p‖ ≤ 1) :
    ((min ⌊(p 0 + 1) * B / 2⌋₊ (B - 1) : ℕ) : ℝ) ≤ (p 0 + 1) * B / 2 ∧
      (p 0 + 1) * B / 2 ≤ ((min ⌊(p 0 + 1) * B / 2⌋₊ (B - 1) : ℕ) : ℝ) + 1 := by
  have hp0 := (e507u_coord_le p 0).trans hp
  rw [abs_le] at hp0
  have hv0 : 0 ≤ (p 0 + 1) * B / 2 := by
    have : (0 : ℝ) ≤ B := by positivity
    have : 0 ≤ p 0 + 1 := by linarith
    positivity
  have hvB : (p 0 + 1) * B / 2 ≤ B := by
    have : (0 : ℝ) ≤ B := by positivity
    nlinarith
  rcases le_total ⌊(p 0 + 1) * B / 2⌋₊ (B - 1) with h | h
  · rw [min_eq_left h]
    exact ⟨Nat.floor_le hv0, (Nat.lt_floor_add_one _).le⟩
  · rw [min_eq_right h]
    have h1 : ((B - 1 : ℕ) : ℝ) ≤ (⌊(p 0 + 1) * B / 2⌋₊ : ℝ) := by exact_mod_cast h
    have h2 := Nat.floor_le hv0
    have h3 : ((B - 1 : ℕ) : ℝ) + 1 = B := by
      rw [Nat.cast_sub hB]; push_cast; ring
    constructor <;> linarith

lemma e507u_min_le (n : ℕ) (hn : 3 ≤ n) (S : Finset ℝ²) (hcard : S.card = n)
    (hball : (S : Set ℝ²) ⊆ Metric.closedBall (0 : ℝ²) 1) : minTriangleArea S ≤ 24 / n := by
  classical
  set B := (n - 1) / 2 with hBdef
  have hB : 1 ≤ B := by omega
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hnorm : ∀ p ∈ S, ‖p‖ ≤ 1 := fun p hp => mem_closedBall_zero_iff.mp (hball hp)
  let f : ℝ² → ℕ := fun p => min ⌊(p 0 + 1) * B / 2⌋₊ (B - 1)
  have hf : ∀ p ∈ S, f p ∈ Finset.range B := fun p _ => Finset.mem_range.mpr (by
    have := min_le_right ⌊(p 0 + 1) * B / 2⌋₊ (B - 1); simp only [f]; omega)
  obtain ⟨j, -, hj⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to (n := 2) hf
    (by rw [Finset.card_range, hcard]; omega)
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp hj
  rw [Finset.mem_filter] at ha hb hc
  have hclose : ∀ p q, p ∈ S → q ∈ S → f p = f q → |p 0 - q 0| ≤ 2 / B := by
    intro p q hpS hqS hpq
    obtain ⟨hp1, hp2⟩ := e507u_bucket B hB p (hnorm p hpS)
    obtain ⟨hq1, hq2⟩ := e507u_bucket B hB q (hnorm q hqS)
    have hpq' : ((f p : ℕ) : ℝ) = ((f q : ℕ) : ℝ) := by rw [hpq]
    simp only [f] at hpq'
    have hv : |(p 0 + 1) * B / 2 - (q 0 + 1) * B / 2| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    have heq : p 0 - q 0 = (2 / B) * ((p 0 + 1) * B / 2 - (q 0 + 1) * B / 2) := by
      field_simp; ring
    rw [heq, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / B)]
    calc 2 / B * |(p 0 + 1) * B / 2 - (q 0 + 1) * B / 2| ≤ 2 / B * 1 :=
          mul_le_mul_of_nonneg_left hv (by positivity)
      _ = 2 / B := mul_one _
  have harea := e507u_area a b c (2 / B) (hnorm a ha.1) (hnorm b hb.1) (hnorm c hc.1)
    (hclose a c ha.1 hc.1 (ha.2.trans hc.2.symm)) (hclose b c hb.1 hc.1 (hb.2.trans hc.2.symm))
  have hmin : minTriangleArea S ≤ |EuclideanGeometry.triangle_area a b c| := by
    unfold minTriangleArea
    refine csInf_le ⟨0, ?_⟩ ⟨![a, b, c], ?_, ?_, rfl⟩
    · rintro _ ⟨q, -, -, rfl⟩; exact abs_nonneg _
    · intro i k hik
      fin_cases i <;> fin_cases k <;> first | rfl | (exfalso; simp_all)
    · intro i; fin_cases i
      · exact ha.1
      · exact hb.1
      · exact hc.1
  have hBn : (n : ℝ) ≤ 6 * B := by
    have : n ≤ 6 * B := by omega
    exact_mod_cast this
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  calc minTriangleArea S ≤ 2 * (2 / B) := hmin.trans harea
    _ ≤ 24 / n := by
        rw [← mul_div_assoc, div_le_div_iff₀ hB' hn']
        linarith

theorem e507u_main : α ≪ (fun n ↦ 1 / (n : ℝ)) := by
  refine IsBigO.of_bound 24 ?_
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnonneg : 0 ≤ α n := by
    apply Real.sSup_nonneg
    rintro _ ⟨S, -, rfl⟩
    apply Real.sInf_nonneg
    rintro _ ⟨q, -, -, rfl⟩
    exact abs_nonneg _
  have hle : α n ≤ 24 / n := by
    apply Real.sSup_le _ (by positivity)
    rintro _ ⟨S, ⟨hcard, hball, -⟩, rfl⟩
    exact e507u_min_le n hn S hcard hball
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnonneg,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / n)]
  calc α n ≤ 24 / n := hle
    _ = 24 * (1 / n) := by ring

/--
It is trivial that $\alpha(n) \ll 1/n$.
-/
@[category research solved, AMS 51]
theorem erdos_507.variants.upper_trivial : α ≪ (fun n ↦ 1 / (n : ℝ)) := by
  exact e507u_main

/--
Erdős observed that $\alpha(n) \gg 1/n^2$.
-/
@[category research solved, AMS 51]
theorem erdos_507.variants.lower_erdos : α ≫ (fun n ↦ 1 / (n : ℝ) ^ 2) := by
  sorry

/--
Current best lower bound [KPS82].
-/
@[category research solved, AMS 51]
theorem erdos_507.variants.lower_kps82 : lowerBest ≪ α := by
  sorry

/--
Current best upper bound [CPZ24]: $\alpha(n) \ll n^{-7/6 + o(1)}$.
-/
@[category research solved, AMS 51]
theorem erdos_507.variants.upper_cpz24 :
    ∃ (o : ℕ → ℝ), Tendsto o atTop (𝓝 0) ∧
    α ≪ (fun n ↦ upperBarrier n * (n : ℝ) ^ o n) := by
  sorry

end Erdos507
