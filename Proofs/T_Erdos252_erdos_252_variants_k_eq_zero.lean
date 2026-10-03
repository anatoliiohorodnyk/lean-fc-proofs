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
public import FormalConjectures.Wikipedia.Schinzel

/-!
# Erdős Problem 252

*References:*
 - [erdosproblems.com/252](https://www.erdosproblems.com/252)
 - [ErSt71] Erdös, P., and E. G. Straus. "Some number theoretic results." Pacific J. Math 36 (1971):
    635-646.
 - [ErSt74] Erdős, Paul, and Ernst Straus. "On the irrationality of certain series." Pacific journal
    of mathematics 55.1 (1974): 85-92.
 - [ErKa54] P. Erdős, M. Kac, Amer. Math. Monthly 61 (1954), Problem 4518.
 - [ScPu06] Schlage-Puchta, J. C., The irrationality of a number theoretical series. Ramanujan J.
    (2006), 455-460.
 - [FLC07] Friedlander, J. B. and Luca, F. and Stoiciu, M., On the irrationality of a divisor
    function series. Integers (2007).
 - [Pr22] Pratt, K., The irrationality of a divisor function series of Erdős and Kac.
    arXiv:2209.11124 (2022).
-/

@[expose] public section

open scoped Nat ArithmeticFunction.sigma

namespace Erdos252


/-- The series `∑ σ k n / n!`. -/
noncomputable def erdos_252_sum (k : ℕ) : ℝ := ∑' n, σ k n / (n ! : ℝ)

/-- Erdős Problem 252: irrationality of the sum for a given $k$. -/
@[category research open, AMS 11]
theorem erdos_252 :
    answer(sorry) ↔ ∀ k ≥ 1, Irrational (erdos_252_sum k) := by
  sorry

lemma e252_card_div (n : ℕ) : (n.divisors).card ≤ n / 2 + 1 := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp
  have hsub : n.divisors ⊆ insert n (Finset.Icc 1 (n / 2)) := by
    intro d hd
    rw [Nat.mem_divisors] at hd
    obtain ⟨⟨c, hc⟩, -⟩ := hd
    rw [Finset.mem_insert, Finset.mem_Icc]
    rcases Nat.lt_or_ge c 2 with h | h
    · interval_cases c
      · omega
      · left; omega
    · right
      have hd0 : 0 < d := by rcases Nat.eq_zero_or_pos d with h' | h' <;> [subst h'; exact h'] <;> omega
      refine ⟨hd0, ?_⟩
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      nlinarith
  calc (n.divisors).card ≤ (insert n (Finset.Icc 1 (n / 2))).card := Finset.card_le_card hsub
    _ ≤ (Finset.Icc 1 (n / 2)).card + 1 := Finset.card_insert_le _ _
    _ = n / 2 + 1 := by simp

lemma e252_a_le (n : ℕ) : (σ 0 n : ℝ) ≤ n / 2 + 1 := by
  rw [ArithmeticFunction.sigma_zero_apply]
  have h := e252_card_div n
  have : ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) / 2 := Nat.cast_div_le
  have h' : ((n.divisors.card : ℕ) : ℝ) ≤ ((n / 2 + 1 : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  linarith

lemma e252_summable : Summable (fun n : ℕ => (σ 0 n : ℝ) / (n ! : ℝ)) := by
  refine (Real.summable_pow_div_factorial 2).of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h1 := e252_a_le n
  have h2 : (n : ℝ) / 2 + 1 ≤ 2 ^ n := by
    have : (n : ℝ) + 1 ≤ 2 ^ n := by
      have := Nat.lt_two_pow_self (n := n)
      exact_mod_cast this
    linarith
  linarith

lemma e252_fact (N j : ℕ) : (N ! : ℝ) * (N + 1) ^ j * (N + 1 + j) ≤ ((N + 1 + j) ! : ℝ) := by
  have h1 := Nat.factorial_mul_pow_le_factorial (m := N) (n := j)
  have h2 : (N + 1 + j)! = (N + 1 + j) * (N + j)! := by
    rw [show N + 1 + j = (N + j) + 1 by ring, Nat.factorial_succ]
  have h3 : N ! * (N + 1) ^ j * (N + 1 + j) ≤ (N + 1 + j)! := by
    rw [h2]; nlinarith
  exact_mod_cast h3

lemma e252_term (N j : ℕ) :
    (σ 0 (N + 1 + j) : ℝ) * (N ! : ℝ) / ((N + 1 + j) ! : ℝ) ≤
      (1 / 2 + 1 / (N + 1)) * (1 / (N + 1 : ℝ)) ^ j := by
  have hf := e252_fact N j
  have ha := e252_a_le (N + 1 + j)
  have hpos1 : (0 : ℝ) < N ! := by exact_mod_cast Nat.factorial_pos N
  have hpos2 : (0 : ℝ) < (N + 1) ^ j := by positivity
  have hpos3 : (0 : ℝ) < N + 1 + j := by positivity
  have hfp : (0 : ℝ) < ((N + 1 + j) ! : ℝ) := by exact_mod_cast Nat.factorial_pos _
  rw [div_le_iff₀ hfp]
  push_cast at ha
  calc (σ 0 (N + 1 + j) : ℝ) * N ! ≤ ((N + 1 + j : ℝ) / 2 + 1) * N ! := by gcongr
    _ ≤ (1 / 2 + 1 / (N + 1)) * (1 / (N + 1 : ℝ)) ^ j * (N ! * (N + 1) ^ j * (N + 1 + j)) := by
        rw [div_pow, one_pow]
        field_simp
        have : (0 : ℝ) ≤ j := by positivity
        nlinarith [hpos1]
    _ ≤ _ := by gcongr

/-- `∑ σ 0 n / n!` is irrational. This is proved in [ErSt71]. -/
@[category research solved, AMS 11]
theorem erdos_252.variants.k_eq_zero : Irrational (erdos_252_sum 0) := by
  rintro ⟨r, hr⟩
  set N := r.den + 4 with hN
  let f : ℕ → ℝ := fun n => (σ 0 n : ℝ) / (n ! : ℝ)
  have hs : Summable f := e252_summable
  have hsplit := (hs.sum_add_tsum_nat_add (N + 1)).symm
  have hx : erdos_252_sum 0 = ∑' n, f n := rfl
  set T := ∑' j, f (j + (N + 1)) with hT
  have hs' : Summable (fun j => f (j + (N + 1))) := (summable_nat_add_iff (N + 1)).mpr hs
  have hNf : (0 : ℝ) < N ! := by exact_mod_cast Nat.factorial_pos N
  -- bounds on N! * T
  have hterm : ∀ j, (N ! : ℝ) * f (j + (N + 1)) ≤ (1 / 2 + 1 / (N + 1)) * (1 / (N + 1 : ℝ)) ^ j := by
    intro j
    have := e252_term N j
    simp only [f]
    rw [show j + (N + 1) = N + 1 + j by ring]
    calc (N ! : ℝ) * ((σ 0 (N + 1 + j) : ℝ) / ((N + 1 + j) ! : ℝ)) =
        (σ 0 (N + 1 + j) : ℝ) * (N ! : ℝ) / ((N + 1 + j) ! : ℝ) := by ring
      _ ≤ _ := this
  have hr1 : (1 / (N + 1 : ℝ)) < 1 := by
    rw [div_lt_one (by positivity)]
    have : (4 : ℝ) ≤ N := by exact_mod_cast (show 4 ≤ N by omega)
    linarith
  have hgeo : Summable (fun j : ℕ => (1 / 2 + 1 / (N + 1 : ℝ)) * (1 / (N + 1 : ℝ)) ^ j) :=
    (summable_geometric_of_lt_one (by positivity) hr1).mul_left _
  have hTle : (N ! : ℝ) * T ≤ (1 / 2 + 1 / (N + 1 : ℝ)) * (1 - 1 / (N + 1 : ℝ))⁻¹ := by
    rw [hT, ← tsum_mul_left, ← tsum_geometric_of_lt_one (by positivity) hr1, ← tsum_mul_left]
    exact Summable.tsum_le_tsum hterm (hs'.mul_left _) hgeo
  have hTlt : (N ! : ℝ) * T < 1 := by
    refine lt_of_le_of_lt hTle ?_
    have hN4 : (4 : ℝ) ≤ N := by exact_mod_cast (show 4 ≤ N by omega)
    have h1 : (1 - 1 / (N + 1 : ℝ))⁻¹ = (N + 1) / N := by
      rw [show (1 : ℝ) - 1 / (N + 1) = N / (N + 1) by field_simp; ring, inv_div]
    rw [h1]
    rw [show (1 / 2 + 1 / (N + 1 : ℝ)) * ((N + 1) / N) = (N + 3) / (2 * N) by field_simp; ring]
    rw [div_lt_one (by positivity)]
    linarith
  have hTpos : 0 < (N ! : ℝ) * T := by
    apply mul_pos hNf
    rw [hT]
    refine hs'.tsum_pos (fun j => by simp only [f]; positivity) 0 ?_
    simp only [f, zero_add]
    apply div_pos _ (by positivity)
    rw [ArithmeticFunction.sigma_zero_apply]
    exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd _, by omega⟩⟩
  -- integrality
  obtain ⟨m1, hm1⟩ : ∃ m : ℤ, (N ! : ℝ) * (r : ℝ) = m := by
    obtain ⟨c, hc⟩ := Nat.dvd_factorial r.den_pos (show r.den ≤ N by omega)
    refine ⟨c * r.num, ?_⟩
    rw [hc, Rat.cast_def]
    push_cast
    field_simp
  obtain ⟨m2, hm2⟩ : ∃ m : ℕ, (N ! : ℝ) * ∑ i ∈ Finset.range (N + 1), f i = m := by
    refine ⟨∑ i ∈ Finset.range (N + 1), σ 0 i * (N ! / i !), ?_⟩
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [Nat.cast_div (Nat.factorial_dvd_factorial (by omega)) (by positivity)]
    simp only [f]
    ring
  have hz : (N ! : ℝ) * T = (m1 - m2 : ℤ) := by
    push_cast
    rw [← hm1, ← hm2, hr, hx, hsplit]
    ring
  rw [hz] at hTpos hTlt
  have h1 : (0 : ℤ) < m1 - m2 := by exact_mod_cast hTpos
  have h2 : m1 - m2 < (1 : ℤ) := by exact_mod_cast hTlt
  omega

/-- `∑ σ 1 n / n!` is irrational. This is proved in [ErSt74]. -/
@[category research solved, AMS 11]
theorem erdos_252.variants.k_eq_one : Irrational (erdos_252_sum 1) := by
  sorry


/-- `∑ σ 2 n / n!` is irrational. This is proved in [ErKa54]. -/
@[category research solved, AMS 11]
theorem erdos_252.variants.k_eq_two : Irrational (erdos_252_sum 2) := by
  sorry

/-- `∑ σ 3 n / n!` is irrational. This is proved in [ScPu06] and [FLC07]. -/
@[category research solved, AMS 11]
theorem erdos_252.variants.k_eq_three : Irrational (erdos_252_sum 3) := by
  sorry

/-- `∑ σ 4 n / n!` is irrational. This is proved in [Pr22]. -/
@[category research solved, AMS 11]
theorem erdos_252.variants.k_eq_four : Irrational (erdos_252_sum 4) := by
  sorry

/-- For a fixed `k ≥ 5`, is `∑ σ k n / n!` irrational?. -/
@[category research open, AMS 11]
theorem erdos_252.variants.k_ge_five :
    answer(sorry) ↔ ∀ k ≥ 5, Irrational (erdos_252_sum k) := by
  sorry

/-- If Schinzel's conjecture is true, then `∑ σ k n / n!` is irrational for all `k`. This is proved
in [ScPu06]. -/
@[category research solved, AMS 11]
theorem erdos_252.variants.schinzel (hs : ∀ (fs : Finset (Polynomial ℤ)),
    (∀ f ∈ fs, BunyakovskyCondition f) → SchinzelCondition fs →
    Infinite ↑{n | ∀ f ∈ fs, Prime (Polynomial.eval (↑n) f).natAbs}) :
    ∀ k, Irrational (erdos_252_sum k) := by
  sorry

/-- If the prime `k`-tuples conjecture is true, then `∑ σ k n / n!` is irrational. This is proved
in [FLC07]. -/
@[category research solved, AMS 11]
theorem erdos_252.variants.prime_tuples {k : ℕ} (hk : 4 ≤ k) (hp : ∀ (a : Fin k → ℕ+)
    (b : Fin k → ℕ) (hab : ∀ p, p.Prime → ∃ n, ¬ p ∣ ∏ i, (a i * n + b i)),
    Set.Infinite {n | ∀ i : Fin k, (a i * n + b i).Prime} ) :
    Irrational (erdos_252_sum k) := by
  sorry

end Erdos252
