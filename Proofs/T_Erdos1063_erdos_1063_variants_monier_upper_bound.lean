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
# Erdős Problem 1063

*References:*
 * [erdosproblems.com/1063](https://www.erdosproblems.com/1063)
 * [ErSe83] Erdos, P. and Selfridge, J. L., Problem 6447. Amer. Math. Monthly (1983), 710.
 * [Gu04] Guy, Richard K., _Unsolved problems in number theory_. (2004), Problem B31.
 * [Mo85] Monier, Jean-Marie, _Problems and Solutions: Solutions of Advanced Problems: 6447_.
   Amer. Math. Monthly **92** (1985), 435-436.
-/

@[expose] public section

open Filter Real
open scoped Nat Topology

namespace Erdos1063

/--
Let $n_k$ be the least $n \ge 2k$ such that all but one of the integers $n - i$ with
$0 \le i < k$ divide $\binom{n}{k}$.
-/
noncomputable def n (k : ℕ) : ℕ :=
  sInf {m | 2 * k ≤ m ∧ ∃ i0 < k, ¬ (m - i0) ∣ m.choose k ∧
    ∀ i < k, i ≠ i0 → (m - i) ∣ m.choose k}

/--
Estimate $n_k$ by finding a better upper bound than Cambie's
$n_k \leq k \cdot \operatorname{lcm}(1, \dotsc, k-1)$.

The comparator takes its least common multiple in `ℕ` and casts the result. Writing the
ascription as `((… ).lcm (fun n : ℕ => n) : ℝ)` instead puts it on the `Finset.lcm`
application, so the coercion lands on `n` and the `lcm` is taken in `ℝ`, where `lcm` of
non-zero elements is `1` and the whole comparator collapses to `k`. -/
@[category research open, AMS 11]
theorem erdos_1063.better_upper :
    let upper_bound : ℕ → ℝ := answer(sorry)
    (fun k => (n k : ℝ)) =O[atTop] upper_bound ∧
    upper_bound =o[atTop] fun k =>
      (k : ℝ) * (((Finset.Icc 1 (k - 1)).lcm id : ℕ) : ℝ) := by
  sorry

/--
Erdős and Selfridge noted that, for $n \ge 2k$ with $k \ge 2$, at least one of the numbers
$n - i$ for $0 \le i < k$ fails to divide $\binom{n}{k}$ ([ErSe83]).
-/
@[category research solved, AMS 11]
theorem erdos_1063.variants.exists_exception {n k : ℕ} (hk : 2 ≤ k) (h : 2 * k ≤ n) :
    ∃ i < k, ¬ (n - i) ∣ n.choose k := by
  sorry

/-- The initial values satisfy $n_2 = 4$, $n_3 = 6$, $n_4 = 9$, and $n_5 = 12$ ([Gu04], Problem B31). -/
@[category research solved, AMS 11]
theorem erdos_1063.variants.small_values :
    n 2 = 4 ∧ n 3 = 6 ∧ n 4 = 9 ∧ n 5 = 12 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- n 2 = 4 : every element of the set is ≥ 2 * 2 = 4, and 4 itself lies in the set
    apply le_antisymm
    · exact Nat.sInf_le (by decide)
    · apply le_csInf ⟨4, by decide⟩
      rintro b hb
      have : 2 * 2 ≤ b := hb.1
      omega
  · -- n 3 = 6
    apply le_antisymm
    · exact Nat.sInf_le (by decide)
    · apply le_csInf ⟨6, by decide⟩
      rintro b hb
      have : 2 * 3 ≤ b := hb.1
      omega
  · -- n 4 = 9 : the only candidate below 9 is m = 8, where both 8 and 6 fail to divide C(8,4) = 70
    apply le_antisymm
    · exact Nat.sInf_le (by decide)
    · apply le_csInf ⟨9, by decide⟩
      rintro b hb
      have hb8 : 8 ≤ b := by have := hb.1; omega
      by_contra! h
      interval_cases b
      · exact absurd hb (by decide)
  · -- n 5 = 12 : the candidates below 12 are m = 10, 11, both of which fail
    apply le_antisymm
    · exact Nat.sInf_le (by decide)
    · apply le_csInf ⟨12, by decide⟩
      rintro b hb
      have hb10 : 10 ≤ b := by have := hb.1; omega
      by_contra! h
      interval_cases b
      · exact absurd hb (by decide)
      · exact absurd hb (by decide)

open Finset in
lemma alt_choose_inv (K : ℕ) : ∀ x : ℚ, (∀ i ≤ K, x - i ≠ 0) →
    ∑ i ∈ range (K + 1), (-1 : ℚ) ^ i * K.choose i / (x - i)
      = (-1) ^ K * K.factorial / ∏ i ∈ range (K + 1), (x - i) := by
  induction K with
  | zero => intro x _; simp
  | succ K ih =>
    intro x hx
    have h1 := ih x (fun i hi => hx i (by omega))
    have h2 := ih (x - 1) (fun i hi => by
      have := hx (i + 1) (by omega); push_cast at this; convert this using 1; ring)
    -- split the binomial coefficient
    have split : ∑ i ∈ range (K + 1 + 1), (-1 : ℚ) ^ i * (K + 1).choose i / (x - i)
        = ∑ i ∈ range (K + 1), (-1 : ℚ) ^ i * K.choose i / (x - i)
          - ∑ i ∈ range (K + 1), (-1 : ℚ) ^ i * K.choose i / (x - 1 - i) := by
      set f : ℕ → ℚ := fun i => (-1 : ℚ) ^ i * K.choose i / (x - i) with hf
      have hA : ∑ i ∈ range (K + 1 + 1), f i = ∑ i ∈ range (K + 1), f i := by
        rw [sum_range_succ]; simp [hf]
      have hB : ∑ i ∈ range (K + 1 + 1), f i = ∑ i ∈ range (K + 1), f (i + 1) + f 0 :=
        sum_range_succ' _ _
      have hterm : ∀ i ∈ range (K + 1), (-1 : ℚ) ^ (i + 1) * (K + 1).choose (i + 1) / (x - ↑(i + 1))
          = -((-1 : ℚ) ^ i * K.choose i / (x - 1 - i)) + f (i + 1) := by
        intro i _
        simp only [hf, Nat.choose_succ_succ', Nat.cast_add]
        push_cast
        ring_nf
      rw [sum_range_succ', sum_congr rfl hterm, sum_add_distrib, sum_neg_distrib, ← hA, hB]
      simp [hf]
      ring
    rw [split, h1, h2]
    -- products
    have hp1 : ∏ i ∈ range (K + 1 + 1), (x - i) = x * ∏ i ∈ range (K + 1), (x - 1 - i) := by
      rw [prod_range_succ', mul_comm]
      congr 1
      · simp
      · refine prod_congr rfl (fun i _ => by push_cast; ring)
    have hp2 : ∏ i ∈ range (K + 1), (x - 1 - i)
        = (∏ i ∈ range K, (x - 1 - i)) * (x - 1 - K) := prod_range_succ _ _
    have hp3 : ∏ i ∈ range (K + 1), (x - i) = x * ∏ i ∈ range K, (x - 1 - i) := by
      rw [prod_range_succ', mul_comm]
      congr 1
      · simp
      · refine prod_congr rfl (fun i _ => by push_cast; ring)
    rw [hp1, hp3, hp2]
    have hx0 : x ≠ 0 := by simpa using hx 0 (by omega)
    have hxK : x - 1 - K ≠ 0 := by
      have := hx (K + 1) le_rfl; push_cast at this; convert this using 1; ring
    have hR : ∏ i ∈ range K, (x - 1 - i) ≠ 0 := by
      rw [prod_ne_zero_iff]; intro i hi
      have := hx (i + 1) (by simp at hi; omega); push_cast at this; convert this using 1; ring
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring

lemma exists_exception_aux {n k : ℕ} (hk : 2 ≤ k) (h : 2 * k ≤ n) :
    ∃ i < k, ¬ (n - i) ∣ n.choose k := by
  by_contra hcon
  push Not at hcon
  obtain ⟨K, rfl⟩ : ∃ K, k = K + 1 := ⟨k - 1, by omega⟩
  choose q hq using hcon
  -- q i is defined for i < K+1; extend
  set Q : ℕ → ℕ := fun i => if hi : i < K + 1 then q i hi else 0 with hQ
  have hQi : ∀ i < K + 1, n.choose (K + 1) = (n - i) * Q i := by
    intro i hi; simp only [hQ, dif_pos hi]; exact hq i hi
  have hx : ∀ i ≤ K, (n : ℚ) - i ≠ 0 := by
    intro i hi
    have : (i : ℚ) < n := by exact_mod_cast (show i < n by omega)
    linarith
  have hid := alt_choose_inv K (n : ℚ) hx
  -- left side times D is an integer
  set D : ℕ := n.choose (K + 1)
  have hD0 : (D : ℚ) ≠ 0 := by
    have : 0 < D := Nat.choose_pos (by omega)
    exact_mod_cast this.ne'
  set z : ℤ := ∑ i ∈ Finset.range (K + 1), (-1 : ℤ) ^ i * K.choose i * Q i
  have hz : (D : ℚ) * ∑ i ∈ Finset.range (K + 1), (-1 : ℚ) ^ i * K.choose i / (n - i) = z := by
    rw [Finset.mul_sum]
    simp only [z]
    push_cast
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi' : i < K + 1 := Finset.mem_range.mp hi
    have hni : ((n - i : ℕ) : ℚ) = (n : ℚ) - i := by rw [Nat.cast_sub (by omega)]
    have hDq : (D : ℚ) = ((n : ℚ) - i) * Q i := by
      rw [← hni]; exact_mod_cast hQi i hi'
    have hne : (n : ℚ) - i ≠ 0 := hx i (by omega)
    rw [hDq]
    field_simp
  -- right side
  have hprod : ∏ i ∈ Finset.range (K + 1), ((n : ℚ) - i) = (K + 1).factorial * D := by
    have h1 : ((n.descFactorial (K + 1) : ℕ) : ℚ) = ∏ i ∈ Finset.range (K + 1), ((n : ℚ) - i) := by
      rw [Nat.descFactorial_eq_prod_range]
      push_cast
      refine Finset.prod_congr rfl (fun i hi => ?_)
      rw [Nat.cast_sub (by simp at hi; omega)]
    rw [← h1, Nat.descFactorial_eq_factorial_mul_choose]
    push_cast; rfl
  rw [hid, hprod] at hz
  have hkey : (z : ℚ) * (K + 1) = (-1) ^ K := by
    rw [← hz, Nat.factorial_succ]
    push_cast
    field_simp
  have hkeyZ : z * (K + 1) = (-1) ^ K := by exact_mod_cast hkey
  rcases neg_one_pow_eq_or ℤ K with h1 | h1 <;> rw [h1] at hkeyZ
  · rcases lt_trichotomy z 0 with hz0 | hz0 | hz0
    · nlinarith
    · rw [hz0] at hkeyZ; simp at hkeyZ
    · nlinarith
  · rcases lt_trichotomy z 0 with hz0 | hz0 | hz0
    · nlinarith
    · rw [hz0] at hkeyZ; simp at hkeyZ
    · nlinarith

open Finset in
lemma monier_dvd {k i : ℕ} (hi1 : 1 ≤ i) (hik : i < k) :
    (k.factorial - i) ∣ k.factorial.choose k := by
  set N := k.factorial
  have hN : 0 < N := Nat.factorial_pos k
  have h1 : N.choose k * k.factorial = ∏ j ∈ range k, (N - j) := by
    rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_prod_range]
  have h0 : (0 : ℕ) ∈ range k := mem_range.mpr (by omega)
  have hi : i ∈ (range k).erase 0 := mem_erase.mpr ⟨by omega, mem_range.mpr hik⟩
  rw [← mul_prod_erase _ _ h0, ← mul_prod_erase _ _ hi] at h1
  simp only [Nat.sub_zero] at h1
  refine ⟨∏ j ∈ ((range k).erase 0).erase i, (N - j), ?_⟩
  have : N.choose k * N = N * ((N - i) * ∏ j ∈ ((range k).erase 0).erase i, (N - j)) := h1
  rw [mul_comm N] at this
  exact Nat.eq_of_mul_eq_mul_right hN (by rw [this])

lemma two_mul_le_factorial {k : ℕ} (hk : 3 ≤ k) : 2 * k ≤ k.factorial := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [Nat.factorial_succ]
  have := Nat.self_le_factorial m
  nlinarith

/-- Monier observed that $n_k \le k!$ for $k \ge 3$ ([Mo85]), since $\binom{k!}{k}$ is divisible
by $k! - i$ for $1 \le i < k$.

The hypothesis `3 ≤ k` is necessary. At $k = 2$ the bound is false: $n_2 = 4$ and $2! = 2$. -/
@[category research solved, AMS 11]
theorem erdos_1063.variants.monier_upper_bound {k : ℕ} (hk : 3 ≤ k) :
    n k ≤ k ! := by
  apply Nat.sInf_le
  refine ⟨two_mul_le_factorial hk, 0, by omega, ?_, ?_⟩
  · intro hdvd
    obtain ⟨i, hik, hi⟩ := exists_exception_aux (by omega : 2 ≤ k) (two_mul_le_factorial hk)
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact hi (by simpa using hdvd)
    · exact hi (monier_dvd hpos hik)
  · intro i hik hi0
    exact monier_dvd (by omega) hik

/-- [Cambie observed](https://www.erdosproblems.com/1063) the improved bound
$n_k \le k \cdot \operatorname{lcm}(1, \dotsc, k - 1)$.

The hypothesis `3 ≤ k` is necessary here too. At $k = 2$ the right hand side is
$2 \cdot \operatorname{lcm}(1) = 2$, while $n_2 = 4$.

The source writes the bound as $k[2, 3, \dotsc, k-1]$. That agrees with the range used here,
because including $1$ does not change a least common multiple. -/
@[category research solved, AMS 11]
theorem erdos_1063.variants.cambie_upper_bound {k : ℕ} (hk : 3 ≤ k) :
    n k ≤ k * (Finset.Icc 1 (k - 1)).lcm id := by
  sorry

/-- The least common multiple bound implies $n_k \le \exp((1 + o(1))k)$. -/
@[category research solved, AMS 11]
theorem erdos_1063.variants.exp_upper_bound :
    ∃ f : ℕ → ℝ, Tendsto f atTop (𝓝 0) ∧
      ∀ k, (n k : ℝ) ≤ exp ((1 + f k) * k) := by
  sorry

end Erdos1063
