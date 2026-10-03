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

/--
It is trivial that $\alpha(n) \ll 1/n$.
-/
@[category research solved, AMS 51]
theorem erdos_507.variants.upper_trivial : α ≪ (fun n ↦ 1 / (n : ℝ)) := by
  sorry

noncomputable def e507pt (p x : ℕ) : ℝ² := !₂[(x : ℝ) / (2 * p), ((x ^ 2 % p : ℕ) : ℝ) / (2 * p)]

lemma e507_area (p a b c : ℕ) (hp : 0 < p) :
    EuclideanGeometry.triangle_area (e507pt p a) (e507pt p b) (e507pt p c) =
      ((a : ℝ) * ((b ^ 2 % p : ℕ) - (c ^ 2 % p : ℕ)) - b * ((a ^ 2 % p : ℕ) - (c ^ 2 % p : ℕ)) +
        c * ((a ^ 2 % p : ℕ) - (b ^ 2 % p : ℕ))) / (8 * p ^ 2) := by
  rw [EuclideanGeometry.triangle_area_eq_det, Matrix.det_fin_three]
  simp [e507pt]
  have : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp
  ring

lemma e507_D_ne (p a b c : ℕ) [hp : Fact p.Prime] (ha : a < p) (hb : b < p) (hc : c < p)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ((a : ℤ) * ((b ^ 2 % p : ℕ) - (c ^ 2 % p : ℕ)) - b * ((a ^ 2 % p : ℕ) - (c ^ 2 % p : ℕ)) +
        c * ((a ^ 2 % p : ℕ) - (b ^ 2 % p : ℕ))) ≠ 0 := by
  intro h
  have h' := congrArg (fun z : ℤ => (z : ZMod p)) h
  simp only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_zero,
    ZMod.natCast_mod, Nat.cast_pow] at h'
  have hf : ((a : ZMod p) - b) * ((b : ZMod p) - c) * ((c : ZMod p) - a) = 0 := by
    linear_combination h'
  have hinj : ∀ x y : ℕ, x < p → y < p → x ≠ y → (x : ZMod p) - y ≠ 0 := by
    intro x y hx hy hxy h0
    apply hxy
    have := sub_eq_zero.mp h0
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this
    exact this
  rcases mul_eq_zero.mp hf with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact hinj a b ha hb hab h2
    · exact hinj b c hb hc hbc h2
  · exact hinj c a hc ha (Ne.symm hac) h1

lemma e507_collinear_area {s : Set ℝ²} (hs : Collinear ℝ s) {a b c : ℝ²} (ha : a ∈ s) (hb : b ∈ s)
    (hc : c ∈ s) : EuclideanGeometry.triangle_area a b c = 0 := by
  obtain ⟨p₀, v, hv⟩ := (collinear_iff_exists_forall_eq_smul_vadd s).mp hs
  obtain ⟨ra, rfl⟩ := hv a ha
  obtain ⟨rb, rfl⟩ := hv b hb
  obtain ⟨rc, rfl⟩ := hv c hc
  rw [EuclideanGeometry.triangle_area_eq_det, Matrix.det_fin_three]
  simp only [vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons]
  ring

lemma e507_coord_le (x : ℝ²) (i : Fin 2) : |x i| ≤ ‖x‖ := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  apply Real.le_sqrt_of_sq_le
  simp only [Real.norm_eq_abs, sq_abs]
  change x i ^ 2 ≤ x 0 ^ 2 + x 1 ^ 2
  fin_cases i <;> simp <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]

lemma e507_area_le (a b c : ℝ²) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) :
    |EuclideanGeometry.triangle_area a b c| ≤ 3 := by
  rw [EuclideanGeometry.triangle_area_eq_det, Matrix.det_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
    Matrix.tail_cons]
  simp only [Matrix.vecHead, Matrix.vecTail, mul_one]
  have a0 := (e507_coord_le a 0).trans ha
  have a1 := (e507_coord_le a 1).trans ha
  have b0 := (e507_coord_le b 0).trans hb
  have b1 := (e507_coord_le b 1).trans hb
  have c0 := (e507_coord_le c 0).trans hc
  have c1 := (e507_coord_le c 1).trans hc
  have pm : ∀ x y : ℝ, |x| ≤ 1 → |y| ≤ 1 → |x * y| ≤ 1 := fun x y hx hy => by
    rw [abs_mul]; exact mul_le_one₀ hx (abs_nonneg y) hy
  have t1 := pm _ _ a0 b1
  have t2 := pm _ _ a0 c1
  have t3 := pm _ _ b0 a1
  have t4 := pm _ _ b0 c1
  have t5 := pm _ _ c0 a1
  have t6 := pm _ _ c0 b1
  rw [abs_le] at t1 t2 t3 t4 t5 t6 ⊢
  obtain ⟨t1, t1'⟩ := t1; obtain ⟨t2, t2'⟩ := t2; obtain ⟨t3, t3'⟩ := t3
  obtain ⟨t4, t4'⟩ := t4; obtain ⟨t5, t5'⟩ := t5; obtain ⟨t6, t6'⟩ := t6
  constructor <;> linarith

lemma e507_pt_inj (p : ℕ) (hp : 0 < p) : Function.Injective (e507pt p) := by
  intro x y h
  have := congrArg (fun v : ℝ² => v 0) h
  simp only [e507pt] at this
  have hp' : (0 : ℝ) < 2 * p := by positivity
  have : (x : ℝ) = y := by
    have h2 : (x : ℝ) / (2 * p) = y / (2 * p) := by simpa using this
    field_simp at h2; linarith
  exact_mod_cast this

lemma e507_pt_ball (p x : ℕ) (hp : 0 < p) (hx : x < p) : ‖e507pt p x‖ ≤ 1 := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_one, Fin.sum_univ_two]
  simp only [e507pt, Real.norm_eq_abs, sq_abs]
  change ((x : ℝ) / (2 * p)) ^ 2 + (((x ^ 2 % p : ℕ) : ℝ) / (2 * p)) ^ 2 ≤ 1
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have h1 : (x : ℝ) / (2 * p) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]; have : (x : ℝ) ≤ p := by exact_mod_cast hx.le
    linarith
  have h2 : ((x ^ 2 % p : ℕ) : ℝ) / (2 * p) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : ((x ^ 2 % p : ℕ) : ℝ) ≤ p := by exact_mod_cast (Nat.mod_lt _ hp).le
    linarith
  have h3 : 0 ≤ (x : ℝ) / (2 * p) := by positivity
  have h4 : 0 ≤ ((x ^ 2 % p : ℕ) : ℝ) / (2 * p) := by positivity
  nlinarith

lemma e507_area_ge (p a b c : ℕ) [hp : Fact p.Prime] (ha : a < p) (hb : b < p) (hc : c < p)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    1 / (8 * (p : ℝ) ^ 2) ≤ |EuclideanGeometry.triangle_area (e507pt p a) (e507pt p b) (e507pt p c)| := by
  have hp0 : 0 < p := hp.out.pos
  rw [e507_area p a b c hp0, abs_div]
  have hD := e507_D_ne p a b c ha hb hc hab hbc hac
  set D : ℤ := (a : ℤ) * ((b ^ 2 % p : ℕ) - (c ^ 2 % p : ℕ)) - b * ((a ^ 2 % p : ℕ) - (c ^ 2 % p : ℕ)) +
        c * ((a ^ 2 % p : ℕ) - (b ^ 2 % p : ℕ)) with hDdef
  have hcast : ((a : ℝ) * ((b ^ 2 % p : ℕ) - (c ^ 2 % p : ℕ)) - b * ((a ^ 2 % p : ℕ) - (c ^ 2 % p : ℕ)) +
        c * ((a ^ 2 % p : ℕ) - (b ^ 2 % p : ℕ))) = (D : ℝ) := by
    simp only [hDdef, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
  rw [hcast]
  have h1 : (1 : ℝ) ≤ |(D : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hD
  have hp' : (0 : ℝ) < 8 * (p : ℝ) ^ 2 := by positivity
  rw [abs_of_pos hp']
  exact div_le_div_of_nonneg_right h1 hp'.le

lemma e507_construct (n : ℕ) (hn : 3 ≤ n) : ∃ S : Finset ℝ², (S.card = n ∧
    ↑S ⊆ Metric.closedBall (0 : ℝ²) 1 ∧ ¬ Collinear ℝ (S : Set ℝ²)) ∧
    1 / (32 * (n : ℝ) ^ 2) ≤ minTriangleArea S := by
  obtain ⟨p, hp, hnp, hp2n⟩ := Nat.exists_prime_lt_and_le_two_mul n (by omega)
  haveI : Fact p.Prime := ⟨hp⟩
  have hp0 : 0 < p := hp.pos
  set S := (Finset.range n).image (e507pt p)
  have hmem : ∀ q ∈ S, ∃ x < n, q = e507pt p x := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
    exact ⟨x, Finset.mem_range.mp hx, rfl⟩
  have harea : ∀ a b c, a < n → b < n → c < n → a ≠ b → b ≠ c → a ≠ c →
      1 / (8 * (p : ℝ) ^ 2) ≤
        |EuclideanGeometry.triangle_area (e507pt p a) (e507pt p b) (e507pt p c)| :=
    fun a b c ha hb hc => e507_area_ge p a b c (by omega) (by omega) (by omega)
  have hpt : ∀ x, x < n → e507pt p x ∈ S := fun x hx => Finset.mem_image_of_mem _ (Finset.mem_range.mpr hx)
  refine ⟨S, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [Finset.card_image_of_injective _ (e507_pt_inj p hp0), Finset.card_range]
  · intro q hq
    obtain ⟨x, hx, rfl⟩ := hmem q hq
    rw [mem_closedBall_zero_iff]
    exact e507_pt_ball p x hp0 (by omega)
  · intro hcol
    have := e507_collinear_area hcol (hpt 0 (by omega)) (hpt 1 (by omega)) (hpt 2 (by omega))
    have h := harea 0 1 2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    rw [this, abs_zero] at h
    have : (0 : ℝ) < 1 / (8 * (p : ℝ) ^ 2) := by positivity
    linarith
  · have hle : 1 / (32 * (n : ℝ) ^ 2) ≤ 1 / (8 * (p : ℝ) ^ 2) := by
      have : (p : ℝ) ≤ 2 * n := by exact_mod_cast hp2n
      have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    refine hle.trans (le_csInf ?_ ?_)
    · refine ⟨_, ![e507pt p 0, e507pt p 1, e507pt p 2], ?_, ?_, rfl⟩
      · intro i j hij
        have hinj := e507_pt_inj p hp0
        fin_cases i <;> fin_cases j <;> first
          | rfl
          | (exfalso
             simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
               Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hij
             have := hinj hij
             omega)
      · intro i
        fin_cases i
        · exact hpt 0 (by omega)
        · exact hpt 1 (by omega)
        · exact hpt 2 (by omega)
    · rintro _ ⟨q, hq, hqS, rfl⟩
      obtain ⟨x0, hx0, h0⟩ := hmem _ (hqS 0)
      obtain ⟨x1, hx1, h1⟩ := hmem _ (hqS 1)
      obtain ⟨x2, hx2, h2⟩ := hmem _ (hqS 2)
      rw [h0, h1, h2]
      have hne : ∀ i j : Fin 3, i ≠ j → q i ≠ q j := fun i j hij h => hij (hq h)
      refine harea x0 x1 x2 hx0 hx1 hx2 ?_ ?_ ?_
      · rintro rfl; exact hne 0 1 (by decide) (h0.trans h1.symm)
      · rintro rfl; exact hne 1 2 (by decide) (h1.trans h2.symm)
      · rintro rfl; exact hne 0 2 (by decide) (h0.trans h2.symm)

theorem e507_main : α ≫ (fun n ↦ 1 / (n : ℝ) ^ 2) := by
  refine IsBigO.of_bound 32 ?_
  filter_upwards [eventually_ge_atTop 3] with n hn
  obtain ⟨S, hS, hmin⟩ := e507_construct n hn
  have hbdd : BddAbove (minTriangleArea '' { S : Finset ℝ² |
      S.card = n ∧ ↑S ⊆ Metric.closedBall (0 : ℝ²) 1 ∧ ¬ Collinear ℝ (S : Set ℝ²) }) := by
    refine ⟨3, ?_⟩
    rintro _ ⟨T, ⟨-, hball, -⟩, rfl⟩
    unfold minTriangleArea
    rcases Set.eq_empty_or_nonempty {abs (EuclideanGeometry.triangle_area (p 0) (p 1) (p 2)) |
        (p : Fin 3 → ℝ²) (_ : Function.Injective p) (_ : ∀ i, p i ∈ T)} with he | ⟨y, hy⟩
    · rw [he, Real.sInf_empty]; norm_num
    · refine (csInf_le ⟨0, ?_⟩ hy).trans ?_
      · rintro _ ⟨q, -, -, rfl⟩; exact abs_nonneg _
      · obtain ⟨q, -, hqT, rfl⟩ := hy
        have hb : ∀ i, ‖q i‖ ≤ 1 := fun i => mem_closedBall_zero_iff.mp (hball (hqT i))
        exact e507_area_le _ _ _ (hb 0) (hb 1) (hb 2)
  have hα : 1 / (32 * (n : ℝ) ^ 2) ≤ α n := hmin.trans (le_csSup hbdd ⟨S, hS, rfl⟩)
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hpos : 0 < 1 / (32 * (n : ℝ) ^ 2) := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / (n : ℝ) ^ 2),
    abs_of_pos (hpos.trans_le hα)]
  have : 1 / (n : ℝ) ^ 2 = 32 * (1 / (32 * (n : ℝ) ^ 2)) := by field_simp
  rw [this]
  linarith

/--
Erdős observed that $\alpha(n) \gg 1/n^2$.
-/
@[category research solved, AMS 51]
theorem erdos_507.variants.lower_erdos : α ≫ (fun n ↦ 1 / (n : ℝ) ^ 2) := by
  exact e507_main

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
