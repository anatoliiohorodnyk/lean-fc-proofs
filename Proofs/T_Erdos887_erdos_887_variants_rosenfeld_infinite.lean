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
# Erdős Problem 887

*References:*
* [erdosproblems.com/887](https://www.erdosproblems.com/887)
* [ErRo97] Erdős, Paul and Rosenfeld, Moshe, The factor-difference set of integers. Acta Arith. (1997), 353--359.
-/

@[expose] public section

open Filter Finset Real
namespace Erdos887

/--
Is there an absolute constant $K$ such that, for every $C > 0$, if $n$ is sufficiently large then
$n$ has at most $K$ divisors in $(n^{\frac{1}{2}}, n^{\frac{1}{2}} + C n^{\frac{1}{4}})$.
-/
@[category research open, AMS 11]
theorem erdos_887.parts.i : ∀ C > (0 : ℝ), ∀ᶠ n in atTop,
    #{ d ∈ Ioo ⌊√n⌋₊ ⌈√n + C * n^((1 : ℝ) / 4)⌉₊ | d ∣ n } ≤ answer(sorry) := by
  sorry

/--
Is there an absolute constant $K$ such that, for every $C > 0$, if $n$ is sufficiently large then
$n$ has at most $K$ divisors in $(n^{\frac{1}{2}}, n^{\frac{1}{2}} + C n^{\frac{1}{4}})$.
-/
@[category research open, AMS 11]
theorem erdos_887.parts.ii : ∃ K, ∀ C > (0 : ℝ), ∀ᶠ n in atTop,
    #{ d ∈ Ioo ⌊√n⌋₊ ⌈√n + C * n^((1 : ℝ) / 4)⌉₊ | d ∣ n } ≤ K := by
  sorry

noncomputable def e887S (n : ℕ) : Finset ℕ :=
  {d ∈ Ioo ⌊√(n : ℝ)⌋₊ ⌈√(n : ℝ) + 16 * (n : ℝ) ^ ((1 : ℝ) / 4)⌉₊ | d ∣ n}

lemma e887_mem (n d e W : ℕ) (hn : n = d * e) (hlt : e < d) (hK : (e + 120) ^ 2 < n)
    (hW : W ^ 4 ≤ n) (hd : d ≤ e + 120 + 16 * W) : d ∈ e887S n := by
  unfold e887S
  rw [Finset.mem_filter, Finset.mem_Ioo]
  have hq : (W : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 4) := by
    have h4 : ((1 : ℝ) / 4) = ((4 : ℕ) : ℝ)⁻¹ := by norm_num
    rw [h4, ← Real.pow_rpow_inv_natCast (Nat.cast_nonneg W) (by norm_num : (4 : ℕ) ≠ 0)]
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hW) (by positivity)
  have hlo : ((e : ℝ) + 120) < Real.sqrt n := by
    rw [Real.lt_sqrt (by positivity)]; exact_mod_cast hK
  have hhi : Real.sqrt n < d := by
    rw [Real.sqrt_lt' (by exact_mod_cast (show 0 < d by omega))]
    have : n < d ^ 2 := by rw [hn, sq]; exact Nat.mul_lt_mul_of_pos_left hlt (by omega)
    exact_mod_cast this
  have hd' : (d : ℝ) ≤ e + 120 + 16 * W := by exact_mod_cast hd
  refine ⟨⟨(Nat.floor_lt (Real.sqrt_nonneg _)).mpr hhi, Nat.lt_ceil.mpr (by linarith)⟩,
    Dvd.intro _ hn.symm⟩

lemma e887_W (s : ℕ) : ((s + 20) ^ 2 + 7 * (s + 20)) ^ 4 ≤ ((s + 20) * (s + 21) * (s + 22) * (s + 23) * (s + 24) * (s + 25) * (s + 26) * (s + 27)) := by
  have h : ((s + 20) * (s + 21) * (s + 22) * (s + 23) * (s + 24) * (s + 25) * (s + 26) * (s + 27)) = ((s + 20) ^ 2 + 7 * (s + 20)) ^ 4 + (4482864000 + 1164062160 * s + 125524188 * s ^ 2 + 7194572 * s ^ 3 + 231168 * s ^ 4 + 3948 * s ^ 5 + 28 * s ^ 6) := by ring
  rw [h]; exact Nat.le_add_right _ _

lemma e887_m0 (s : ℕ) : ((s + 22) * (s + 23) * (s + 24) * (s + 25)) ∈ e887S ((s + 20) * (s + 21) * (s + 22) * (s + 23) * (s + 24) * (s + 25) * (s + 26) * (s + 27)) := by
  have h1 : ((s + 22) * (s + 23) * (s + 24) * (s + 25)) = ((s + 20) * (s + 21) * (s + 26) * (s + 27)) + (8760 + 752 * s + 16 * s ^ 2) := by ring
  have h2 : ((s + 22) * (s + 23) * (s + 24) * (s + 25)) * ((s + 20) * (s + 21) * (s + 26) * (s + 27)) = (((s + 20) * (s + 21) * (s + 26) * (s + 27)) + 120) ^ 2 + (2512022400 + 656597520 * s + 71174424 * s ^ 2 + 4095392 * s ^ 3 + 131928 * s ^ 4 + 2256 * s ^ 5 + 16 * s ^ 6) := by ring
  have h3 : ((s + 20) * (s + 21) * (s + 26) * (s + 27)) + 120 + 16 * ((s + 20) ^ 2 + 7 * (s + 20)) = ((s + 22) * (s + 23) * (s + 24) * (s + 25)) + 0 := by ring
  have hn : ((s + 20) * (s + 21) * (s + 22) * (s + 23) * (s + 24) * (s + 25) * (s + 26) * (s + 27)) = ((s + 22) * (s + 23) * (s + 24) * (s + 25)) * ((s + 20) * (s + 21) * (s + 26) * (s + 27)) := by ring
  refine e887_mem _ _ _ _ hn ?_ ?_ (e887_W s) ?_
  · rw [h1]; exact Nat.lt_add_of_pos_right (by positivity)
  · rw [hn, h2]; exact Nat.lt_add_of_pos_right (by positivity)
  · rw [h3]; exact Nat.le_add_right _ _

lemma e887_m1 (s : ℕ) : ((s + 21) * (s + 23) * (s + 24) * (s + 26)) ∈ e887S ((s + 20) * (s + 21) * (s + 22) * (s + 23) * (s + 24) * (s + 25) * (s + 26) * (s + 27)) := by
  have h1 : ((s + 21) * (s + 23) * (s + 24) * (s + 26)) = ((s + 20) * (s + 22) * (s + 25) * (s + 27)) + (4392 + 376 * s + 8 * s ^ 2) := by ring
  have h2 : ((s + 21) * (s + 23) * (s + 24) * (s + 26)) * ((s + 20) * (s + 22) * (s + 25) * (s + 27)) = (((s + 20) * (s + 22) * (s + 25) * (s + 27)) + 120) ^ 2 + (1233129600 + 324378960 * s + 35335928 * s ^ 2 + 2040552 * s ^ 3 + 65888 * s ^ 4 + 1128 * s ^ 5 + 8 * s ^ 6) := by ring
  have h3 : ((s + 20) * (s + 22) * (s + 25) * (s + 27)) + 120 + 16 * ((s + 20) ^ 2 + 7 * (s + 20)) = ((s + 21) * (s + 23) * (s + 24) * (s + 26)) + (4368 + 376 * s + 8 * s ^ 2) := by ring
  have hn : ((s + 20) * (s + 21) * (s + 22) * (s + 23) * (s + 24) * (s + 25) * (s + 26) * (s + 27)) = ((s + 21) * (s + 23) * (s + 24) * (s + 26)) * ((s + 20) * (s + 22) * (s + 25) * (s + 27)) := by ring
  refine e887_mem _ _ _ _ hn ?_ ?_ (e887_W s) ?_
  · rw [h1]; exact Nat.lt_add_of_pos_right (by positivity)
  · rw [hn, h2]; exact Nat.lt_add_of_pos_right (by positivity)
  · rw [h3]; exact Nat.le_add_right _ _

lemma e887_m2 (s : ℕ) : ((s + 21) * (s + 22) * (s + 25) * (s + 26)) ∈ e887S ((s + 20) * (s + 21) * (s + 22) * (s + 23) * (s + 24) * (s + 25) * (s + 26) * (s + 27)) := by
  have h1 : ((s + 21) * (s + 22) * (s + 25) * (s + 26)) = ((s + 20) * (s + 23) * (s + 24) * (s + 27)) + (2220 + 188 * s + 4 * s ^ 2) := by ring
  have h2 : ((s + 21) * (s + 22) * (s + 25) * (s + 26)) * ((s + 20) * (s + 23) * (s + 24) * (s + 27)) = (((s + 20) * (s + 23) * (s + 24) * (s + 27)) + 120) ^ 2 + (590184000 + 157660560 * s + 17377212 * s ^ 2 + 1012004 * s ^ 3 + 32856 * s ^ 4 + 564 * s ^ 5 + 4 * s ^ 6) := by ring
  have h3 : ((s + 20) * (s + 23) * (s + 24) * (s + 27)) + 120 + 16 * ((s + 20) ^ 2 + 7 * (s + 20)) = ((s + 21) * (s + 22) * (s + 25) * (s + 26)) + (6540 + 564 * s + 12 * s ^ 2) := by ring
  have hn : ((s + 20) * (s + 21) * (s + 22) * (s + 23) * (s + 24) * (s + 25) * (s + 26) * (s + 27)) = ((s + 21) * (s + 22) * (s + 25) * (s + 26)) * ((s + 20) * (s + 23) * (s + 24) * (s + 27)) := by ring
  refine e887_mem _ _ _ _ hn ?_ ?_ (e887_W s) ?_
  · rw [h1]; exact Nat.lt_add_of_pos_right (by positivity)
  · rw [hn, h2]; exact Nat.lt_add_of_pos_right (by positivity)
  · rw [h3]; exact Nat.le_add_right _ _

lemma e887_m3 (s : ℕ) : ((s + 21) * (s + 22) * (s + 24) * (s + 27)) ∈ e887S ((s + 20) * (s + 21) * (s + 22) * (s + 23) * (s + 24) * (s + 25) * (s + 26) * (s + 27)) := by
  have h1 : ((s + 21) * (s + 22) * (s + 24) * (s + 27)) = ((s + 20) * (s + 23) * (s + 25) * (s + 26)) + (376 + 16 * s) := by ring
  have h2 : ((s + 21) * (s + 22) * (s + 24) * (s + 27)) * ((s + 20) * (s + 23) * (s + 25) * (s + 26)) = (((s + 20) * (s + 23) * (s + 25) * (s + 26)) + 120) ^ 2 + (40649600 + 11775760 * s + 1271768 * s ^ 2 + 65632 * s ^ 3 + 1640 * s ^ 4 + 16 * s ^ 5) := by ring
  have h3 : ((s + 20) * (s + 23) * (s + 25) * (s + 26)) + 120 + 16 * ((s + 20) ^ 2 + 7 * (s + 20)) = ((s + 21) * (s + 22) * (s + 24) * (s + 27)) + (8384 + 736 * s + 16 * s ^ 2) := by ring
  have hn : ((s + 20) * (s + 21) * (s + 22) * (s + 23) * (s + 24) * (s + 25) * (s + 26) * (s + 27)) = ((s + 21) * (s + 22) * (s + 24) * (s + 27)) * ((s + 20) * (s + 23) * (s + 25) * (s + 26)) := by ring
  refine e887_mem _ _ _ _ hn ?_ ?_ (e887_W s) ?_
  · rw [h1]; exact Nat.lt_add_of_pos_right (by positivity)
  · rw [hn, h2]; exact Nat.lt_add_of_pos_right (by positivity)
  · rw [h3]; exact Nat.le_add_right _ _

lemma e887_o0 (s : ℕ) : ((s + 21) * (s + 23) * (s + 24) * (s + 26)) < ((s + 22) * (s + 23) * (s + 24) * (s + 25)) := by
  have h : ((s + 22) * (s + 23) * (s + 24) * (s + 25)) = ((s + 21) * (s + 23) * (s + 24) * (s + 26)) + (2208 + 188 * s + 4 * s ^ 2) := by ring
  rw [h]; exact Nat.lt_add_of_pos_right (by positivity)

lemma e887_o1 (s : ℕ) : ((s + 21) * (s + 22) * (s + 25) * (s + 26)) < ((s + 21) * (s + 23) * (s + 24) * (s + 26)) := by
  have h : ((s + 21) * (s + 23) * (s + 24) * (s + 26)) = ((s + 21) * (s + 22) * (s + 25) * (s + 26)) + (1092 + 94 * s + 2 * s ^ 2) := by ring
  rw [h]; exact Nat.lt_add_of_pos_right (by positivity)

lemma e887_o2 (s : ℕ) : ((s + 21) * (s + 22) * (s + 24) * (s + 27)) < ((s + 21) * (s + 22) * (s + 25) * (s + 26)) := by
  have h : ((s + 21) * (s + 22) * (s + 25) * (s + 26)) = ((s + 21) * (s + 22) * (s + 24) * (s + 27)) + (924 + 86 * s + 2 * s ^ 2) := by ring
  rw [h]; exact Nat.lt_add_of_pos_right (by positivity)

lemma e887_card4 (S : Finset ℕ) (a b c d : ℕ) (h1 : b < a) (h2 : c < b) (h3 : d < c)
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S) : 4 ≤ S.card := by
  have hsub : ({a, b, c, d} : Finset ℕ) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  refine le_trans (le_of_eq ?_) (Finset.card_le_card hsub)
  rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_insert_of_notMem (by simp; omega),
    Finset.card_pair (by omega)]

/--
A question of Erdős and Rosenfeld, who proved that there are infinitely many $n$ with (at least)
$4$ divisors in $(n^{\frac{1}{2}}, n^{\frac{1}{2}} + cn^{\frac{1}{4}})$.
-/
@[category research solved, AMS 11]
theorem erdos_887.variants.rosenfeld_infinite : ∃ C > (0 : ℝ),
    Infinite {n : ℕ | 4 ≤ #{ d ∈ Ioo ⌊√n⌋₊ ⌈√n + C * n^((1 : ℝ) / 4)⌉₊ | d ∣ n }} := by
  refine ⟨16, by norm_num, ?_⟩
  rw [Set.infinite_coe_iff]
  apply Set.infinite_of_forall_exists_gt
  intro s
  refine ⟨((s + 20) * (s + 21) * (s + 22) * (s + 23) * (s + 24) * (s + 25) * (s + 26) * (s + 27)), ?_, ?_⟩
  · exact e887_card4 _ _ _ _ _ (e887_o0 s) (e887_o1 s) (e887_o2 s) (e887_m0 s) (e887_m1 s)
      (e887_m2 s) (e887_m3 s)
  · have h1 : s < ((s + 20) ^ 2 + 7 * (s + 20)) := by nlinarith
    exact lt_of_lt_of_le h1 ((Nat.le_self_pow (by norm_num) _).trans (e887_W s))

/--
Erdős and Rosenfeld, ask whether $4$ is the best possible $K$ for the infinitude of $n$
with (at least) $K$ divisors in $(n^{\frac{1}{2}}, n^{\frac{1}{2}} + n^{\frac{1}{4}})$.
-/
@[category research open, AMS 11]
theorem erdos_887.variants.rosenfeld_4 :
    IsGreatest {K | ∃ C > (0 : ℝ),
      Infinite {n : ℕ | K ≤ #{ d ∈ Ioo ⌊√n⌋₊ ⌈√n + C * n^((1 : ℝ) / 4)⌉₊ | d ∣ n }}} 4 := by
  sorry

end Erdos887
