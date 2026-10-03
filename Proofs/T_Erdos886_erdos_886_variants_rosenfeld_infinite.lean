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
# Erdős Problem 886

*References:*
- [erdosproblems.com/886](https://www.erdosproblems.com/886)
- [ErRo97] Erdős, Paul and Rosenfeld, Moshe, The factor-difference set of integers. Acta Arith.
  (1997), 353--359.
-/

@[expose] public section

open Nat Filter

namespace Erdos886

/--
The set of divisors of $n$ in the interval $(n^{1/2}, n^{1/2} + n^{1/2-\epsilon})$.
-/
noncomputable def Erdos886Divisors (n : ℕ) (ε : ℝ) (C : ℝ) : Finset ℕ :=
  (divisors n).filter (fun d =>
    (n : ℝ) ^ (1/2 : ℝ) < d ∧ (d : ℝ) < (n : ℝ) ^ (1/2 : ℝ) + C * (n : ℝ) ^ (1/2 - ε))

/--
Let $\epsilon>0$. Is it true that, for all large $n$, the number of divisors of $n$ in
$(n^{1/2},n^{1/2}+n^{1/2-\epsilon})$ is $O_\epsilon(1)$?

Erdős attributes this conjecture to Ruzsa.
-/
@[category research open, AMS 11]
theorem erdos_886 :
    answer(sorry) ↔ ∀ ε > 0, ∃ K : ℕ, ∀ᶠ n in atTop, (Erdos886Divisors n ε 1).card ≤ K := by
  sorry

lemma e886_mem (n d e W : ℕ) (hn : n = d * e) (hlt : e < d) (hK : (e + 120) ^ 2 < n)
    (hW : W ^ 4 ≤ n) (hd : d ≤ e + 120 + 16 * W) : d ∈ Erdos886Divisors n (1/4) 16 := by
  have hn0 : n ≠ 0 := by omega
  unfold Erdos886Divisors
  rw [Finset.mem_filter, Nat.mem_divisors]
  refine ⟨⟨Dvd.intro _ hn.symm, hn0⟩, ?_⟩
  have hsq : (n : ℝ) ^ (1/2 : ℝ) = Real.sqrt n := (Real.sqrt_eq_rpow _).symm
  have hq : (W : ℝ) ≤ (n : ℝ) ^ (1/2 - 1/4 : ℝ) := by
    have h4 : (1/2 - 1/4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ := by norm_num
    rw [h4, ← Real.pow_rpow_inv_natCast (Nat.cast_nonneg W) (by norm_num : (4 : ℕ) ≠ 0)]
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hW) (by positivity)
  have hlo : ((e : ℝ) + 120) < Real.sqrt n := by
    rw [Real.lt_sqrt (by positivity)]; exact_mod_cast hK
  have hhi : Real.sqrt n < d := by
    rw [Real.sqrt_lt' (by exact_mod_cast (show 0 < d by omega))]
    have : n < d ^ 2 := by rw [hn, sq]; exact Nat.mul_lt_mul_of_pos_left hlt (by omega)
    exact_mod_cast this
  have hd' : (d : ℝ) ≤ e + 120 + 16 * W := by exact_mod_cast hd
  rw [hsq]
  constructor <;> linarith

lemma e886_W (s : ℕ) : ((s + 20) ^ 2 + 7 * (s + 20)) ^ 4 ≤ ((s + 20) * (s + 21) * (s + 22) * (s + 23) * (s + 24) * (s + 25) * (s + 26) * (s + 27)) := by
  have h : ((s + 20) * (s + 21) * (s + 22) * (s + 23) * (s + 24) * (s + 25) * (s + 26) * (s + 27)) = ((s + 20) ^ 2 + 7 * (s + 20)) ^ 4 + (4482864000 + 1164062160 * s + 125524188 * s ^ 2 + 7194572 * s ^ 3 + 231168 * s ^ 4 + 3948 * s ^ 5 + 28 * s ^ 6) := by ring
  rw [h]; exact Nat.le_add_right _ _

lemma e886_m0 (s : ℕ) : ((s + 22) * (s + 23) * (s + 24) * (s + 25)) ∈ Erdos886Divisors ((s + 20) * (s + 21) * (s + 22) * (s + 23) * (s + 24) * (s + 25) * (s + 26) * (s + 27)) (1/4) 16 := by
  have h1 : ((s + 22) * (s + 23) * (s + 24) * (s + 25)) = ((s + 20) * (s + 21) * (s + 26) * (s + 27)) + (8760 + 752 * s + 16 * s ^ 2) := by ring
  have h2 : ((s + 22) * (s + 23) * (s + 24) * (s + 25)) * ((s + 20) * (s + 21) * (s + 26) * (s + 27)) = (((s + 20) * (s + 21) * (s + 26) * (s + 27)) + 120) ^ 2 + (2512022400 + 656597520 * s + 71174424 * s ^ 2 + 4095392 * s ^ 3 + 131928 * s ^ 4 + 2256 * s ^ 5 + 16 * s ^ 6) := by ring
  have h3 : ((s + 20) * (s + 21) * (s + 26) * (s + 27)) + 120 + 16 * ((s + 20) ^ 2 + 7 * (s + 20)) = ((s + 22) * (s + 23) * (s + 24) * (s + 25)) + 0 := by ring
  have hn : ((s + 20) * (s + 21) * (s + 22) * (s + 23) * (s + 24) * (s + 25) * (s + 26) * (s + 27)) = ((s + 22) * (s + 23) * (s + 24) * (s + 25)) * ((s + 20) * (s + 21) * (s + 26) * (s + 27)) := by ring
  refine e886_mem _ _ _ _ hn ?_ ?_ (e886_W s) ?_
  · rw [h1]; exact Nat.lt_add_of_pos_right (by positivity)
  · rw [hn, h2]; exact Nat.lt_add_of_pos_right (by positivity)
  · rw [h3]; exact Nat.le_add_right _ _

lemma e886_m1 (s : ℕ) : ((s + 21) * (s + 23) * (s + 24) * (s + 26)) ∈ Erdos886Divisors ((s + 20) * (s + 21) * (s + 22) * (s + 23) * (s + 24) * (s + 25) * (s + 26) * (s + 27)) (1/4) 16 := by
  have h1 : ((s + 21) * (s + 23) * (s + 24) * (s + 26)) = ((s + 20) * (s + 22) * (s + 25) * (s + 27)) + (4392 + 376 * s + 8 * s ^ 2) := by ring
  have h2 : ((s + 21) * (s + 23) * (s + 24) * (s + 26)) * ((s + 20) * (s + 22) * (s + 25) * (s + 27)) = (((s + 20) * (s + 22) * (s + 25) * (s + 27)) + 120) ^ 2 + (1233129600 + 324378960 * s + 35335928 * s ^ 2 + 2040552 * s ^ 3 + 65888 * s ^ 4 + 1128 * s ^ 5 + 8 * s ^ 6) := by ring
  have h3 : ((s + 20) * (s + 22) * (s + 25) * (s + 27)) + 120 + 16 * ((s + 20) ^ 2 + 7 * (s + 20)) = ((s + 21) * (s + 23) * (s + 24) * (s + 26)) + (4368 + 376 * s + 8 * s ^ 2) := by ring
  have hn : ((s + 20) * (s + 21) * (s + 22) * (s + 23) * (s + 24) * (s + 25) * (s + 26) * (s + 27)) = ((s + 21) * (s + 23) * (s + 24) * (s + 26)) * ((s + 20) * (s + 22) * (s + 25) * (s + 27)) := by ring
  refine e886_mem _ _ _ _ hn ?_ ?_ (e886_W s) ?_
  · rw [h1]; exact Nat.lt_add_of_pos_right (by positivity)
  · rw [hn, h2]; exact Nat.lt_add_of_pos_right (by positivity)
  · rw [h3]; exact Nat.le_add_right _ _

lemma e886_m2 (s : ℕ) : ((s + 21) * (s + 22) * (s + 25) * (s + 26)) ∈ Erdos886Divisors ((s + 20) * (s + 21) * (s + 22) * (s + 23) * (s + 24) * (s + 25) * (s + 26) * (s + 27)) (1/4) 16 := by
  have h1 : ((s + 21) * (s + 22) * (s + 25) * (s + 26)) = ((s + 20) * (s + 23) * (s + 24) * (s + 27)) + (2220 + 188 * s + 4 * s ^ 2) := by ring
  have h2 : ((s + 21) * (s + 22) * (s + 25) * (s + 26)) * ((s + 20) * (s + 23) * (s + 24) * (s + 27)) = (((s + 20) * (s + 23) * (s + 24) * (s + 27)) + 120) ^ 2 + (590184000 + 157660560 * s + 17377212 * s ^ 2 + 1012004 * s ^ 3 + 32856 * s ^ 4 + 564 * s ^ 5 + 4 * s ^ 6) := by ring
  have h3 : ((s + 20) * (s + 23) * (s + 24) * (s + 27)) + 120 + 16 * ((s + 20) ^ 2 + 7 * (s + 20)) = ((s + 21) * (s + 22) * (s + 25) * (s + 26)) + (6540 + 564 * s + 12 * s ^ 2) := by ring
  have hn : ((s + 20) * (s + 21) * (s + 22) * (s + 23) * (s + 24) * (s + 25) * (s + 26) * (s + 27)) = ((s + 21) * (s + 22) * (s + 25) * (s + 26)) * ((s + 20) * (s + 23) * (s + 24) * (s + 27)) := by ring
  refine e886_mem _ _ _ _ hn ?_ ?_ (e886_W s) ?_
  · rw [h1]; exact Nat.lt_add_of_pos_right (by positivity)
  · rw [hn, h2]; exact Nat.lt_add_of_pos_right (by positivity)
  · rw [h3]; exact Nat.le_add_right _ _

lemma e886_m3 (s : ℕ) : ((s + 21) * (s + 22) * (s + 24) * (s + 27)) ∈ Erdos886Divisors ((s + 20) * (s + 21) * (s + 22) * (s + 23) * (s + 24) * (s + 25) * (s + 26) * (s + 27)) (1/4) 16 := by
  have h1 : ((s + 21) * (s + 22) * (s + 24) * (s + 27)) = ((s + 20) * (s + 23) * (s + 25) * (s + 26)) + (376 + 16 * s) := by ring
  have h2 : ((s + 21) * (s + 22) * (s + 24) * (s + 27)) * ((s + 20) * (s + 23) * (s + 25) * (s + 26)) = (((s + 20) * (s + 23) * (s + 25) * (s + 26)) + 120) ^ 2 + (40649600 + 11775760 * s + 1271768 * s ^ 2 + 65632 * s ^ 3 + 1640 * s ^ 4 + 16 * s ^ 5) := by ring
  have h3 : ((s + 20) * (s + 23) * (s + 25) * (s + 26)) + 120 + 16 * ((s + 20) ^ 2 + 7 * (s + 20)) = ((s + 21) * (s + 22) * (s + 24) * (s + 27)) + (8384 + 736 * s + 16 * s ^ 2) := by ring
  have hn : ((s + 20) * (s + 21) * (s + 22) * (s + 23) * (s + 24) * (s + 25) * (s + 26) * (s + 27)) = ((s + 21) * (s + 22) * (s + 24) * (s + 27)) * ((s + 20) * (s + 23) * (s + 25) * (s + 26)) := by ring
  refine e886_mem _ _ _ _ hn ?_ ?_ (e886_W s) ?_
  · rw [h1]; exact Nat.lt_add_of_pos_right (by positivity)
  · rw [hn, h2]; exact Nat.lt_add_of_pos_right (by positivity)
  · rw [h3]; exact Nat.le_add_right _ _

lemma e886_o0 (s : ℕ) : ((s + 21) * (s + 23) * (s + 24) * (s + 26)) < ((s + 22) * (s + 23) * (s + 24) * (s + 25)) := by
  have h : ((s + 22) * (s + 23) * (s + 24) * (s + 25)) = ((s + 21) * (s + 23) * (s + 24) * (s + 26)) + (2208 + 188 * s + 4 * s ^ 2) := by ring
  rw [h]; exact Nat.lt_add_of_pos_right (by positivity)

lemma e886_o1 (s : ℕ) : ((s + 21) * (s + 22) * (s + 25) * (s + 26)) < ((s + 21) * (s + 23) * (s + 24) * (s + 26)) := by
  have h : ((s + 21) * (s + 23) * (s + 24) * (s + 26)) = ((s + 21) * (s + 22) * (s + 25) * (s + 26)) + (1092 + 94 * s + 2 * s ^ 2) := by ring
  rw [h]; exact Nat.lt_add_of_pos_right (by positivity)

lemma e886_o2 (s : ℕ) : ((s + 21) * (s + 22) * (s + 24) * (s + 27)) < ((s + 21) * (s + 22) * (s + 25) * (s + 26)) := by
  have h : ((s + 21) * (s + 22) * (s + 25) * (s + 26)) = ((s + 21) * (s + 22) * (s + 24) * (s + 27)) + (924 + 86 * s + 2 * s ^ 2) := by ring
  rw [h]; exact Nat.lt_add_of_pos_right (by positivity)

lemma e886_card4 (S : Finset ℕ) (a b c d : ℕ) (h1 : b < a) (h2 : c < b) (h3 : d < c)
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S) : 4 ≤ S.card := by
  have hsub : ({a, b, c, d} : Finset ℕ) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  refine le_trans (le_of_eq ?_) (Finset.card_le_card hsub)
  rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_insert_of_notMem (by simp; omega),
    Finset.card_pair (by omega)]

/--
Erdős and Rosenfeld [ErRo97] proved that there are infinitely many $n$ such that there are
four divisors of $n$ in $(n^{1/2},n^{1/2}+16n^{1/4})$.
-/
@[category research solved, AMS 11]
theorem erdos_886.variants.rosenfeld_infinite :
    Set.Infinite {n | 4 ≤ (Erdos886Divisors n (1/4) 16).card} := by
  apply Set.infinite_of_forall_exists_gt
  intro s
  refine ⟨((s + 20) * (s + 21) * (s + 22) * (s + 23) * (s + 24) * (s + 25) * (s + 26) * (s + 27)), ?_, ?_⟩
  · exact e886_card4 _ _ _ _ _ (e886_o0 s) (e886_o1 s) (e886_o2 s) (e886_m0 s) (e886_m1 s)
      (e886_m2 s) (e886_m3 s)
  · have h1 : s < ((s + 20) ^ 2 + 7 * (s + 20)) := by nlinarith
    exact lt_of_lt_of_le h1 ((Nat.le_self_pow (by norm_num) _).trans (e886_W s))

/--
Erdős and Rosenfeld [ErRo97] proved that, for any constant $C>0$, all large $n$ have at most
$1+C^2$ many divisors in $[n^{1/2}, n^{1/2}+Cn^{1/4}]$.
-/
@[category research solved, AMS 11]
theorem erdos_886.variants.rosenfeld_bound :
    ∀ C > 0, ∀ᶠ (n : ℕ) in atTop,
    ((divisors n).filter (fun (d : ℕ) =>
      (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d : ℝ) ∧ (d : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) + C * (n : ℝ) ^ (1 / 4 : ℝ))).card
      ≤ 1 + C ^ 2 := by
  sorry

end Erdos886
