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

/-- `∑ σ 0 n / n!` is irrational. This is proved in [ErSt71]. -/
@[category research solved, AMS 11]
theorem erdos_252.variants.k_eq_zero : Irrational (erdos_252_sum 0) := by
  sorry

lemma e252o_card_div (n : ℕ) : (n.divisors).card ≤ n / 2 + 1 := by
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

lemma e252o_a_le (n : ℕ) : (σ 0 n : ℝ) ≤ n / 2 + 1 := by
  rw [ArithmeticFunction.sigma_zero_apply]
  have h := e252o_card_div n
  have : ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) / 2 := Nat.cast_div_le
  have h' : ((n.divisors.card : ℕ) : ℝ) ≤ ((n / 2 + 1 : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  linarith

lemma e252o_summable : Summable (fun n : ℕ => (σ 0 n : ℝ) / (n ! : ℝ)) := by
  refine (Real.summable_pow_div_factorial 2).of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h1 := e252o_a_le n
  have h2 : (n : ℝ) / 2 + 1 ≤ 2 ^ n := by
    have : (n : ℝ) + 1 ≤ 2 ^ n := by
      have := Nat.lt_two_pow_self (n := n)
      exact_mod_cast this
    linarith
  linarith

lemma e252o_fact (N j : ℕ) : (N ! : ℝ) * (N + 1) ^ j * (N + 1 + j) ≤ ((N + 1 + j) ! : ℝ) := by
  have h1 := Nat.factorial_mul_pow_le_factorial (m := N) (n := j)
  have h2 : (N + 1 + j)! = (N + 1 + j) * (N + j)! := by
    rw [show N + 1 + j = (N + j) + 1 by ring, Nat.factorial_succ]
  have h3 : N ! * (N + 1) ^ j * (N + 1 + j) ≤ (N + 1 + j)! := by
    rw [h2]; nlinarith
  exact_mod_cast h3

lemma e252o_term (N j : ℕ) :
    (σ 0 (N + 1 + j) : ℝ) * (N ! : ℝ) / ((N + 1 + j) ! : ℝ) ≤
      (1 / 2 + 1 / (N + 1)) * (1 / (N + 1 : ℝ)) ^ j := by
  have hf := e252o_fact N j
  have ha := e252o_a_le (N + 1 + j)
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


lemma e252o_sig1 (m : ℕ) : (σ 1 m : ℝ) ≤ m * (m / 2 + 1) := by
  rw [ArithmeticFunction.sigma_one_apply]
  have h1 : ∑ d ∈ m.divisors, d ≤ m.divisors.card * m := by
    calc ∑ d ∈ m.divisors, d ≤ ∑ d ∈ m.divisors, m :=
          Finset.sum_le_sum (fun d hd => Nat.divisor_le hd)
      _ = m.divisors.card * m := by rw [Finset.sum_const, smul_eq_mul]
  have h2 := e252o_card_div m
  have h3 : ((m / 2 : ℕ) : ℝ) ≤ (m : ℝ) / 2 := Nat.cast_div_le
  have h4 : ((∑ d ∈ m.divisors, d : ℕ) : ℝ) ≤ ((m.divisors.card * m : ℕ) : ℝ) := by exact_mod_cast h1
  have h5 : ((m.divisors.card : ℕ) : ℝ) ≤ ((m / 2 + 1 : ℕ) : ℝ) := by exact_mod_cast h2
  push_cast at h4 h5 ⊢
  have : (0 : ℝ) ≤ m := by positivity
  nlinarith

lemma e252o_summable1 : Summable (fun n : ℕ => (σ 1 n : ℝ) / (n ! : ℝ)) := by
  refine (Real.summable_pow_div_factorial 4).of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h1 := e252o_sig1 n
  have h2 : (n : ℝ) + 1 ≤ 2 ^ n := by exact_mod_cast Nat.lt_two_pow_self (n := n)
  have h3 : (0 : ℝ) ≤ n := by positivity
  have h4 : (4 : ℝ) ^ n = 2 ^ n * 2 ^ n := by rw [← mul_pow]; norm_num
  nlinarith

lemma e252o_term1 (p i : ℕ) (hp : 1 ≤ p) :
    (σ 1 (p + 1 + i) : ℝ) * ((p - 1) ! : ℝ) / ((p + 1 + i) ! : ℝ) ≤
      (1 / 2 + 3 / (2 * p)) * (1 / (p : ℝ)) ^ i := by
  have hf := e252o_fact (p - 1) i
  have hpp : ((p - 1 : ℕ) : ℝ) + 1 = p := by rw [Nat.cast_sub hp]; ring
  rw [hpp] at hf
  have hm : ((p + 1 + i) ! : ℝ) = (p + 1 + i) * ((p - 1 + 1 + i) ! : ℝ) := by
    rw [show p - 1 + 1 + i = p + i by omega, show p + 1 + i = (p + i) + 1 by ring,
      Nat.factorial_succ]
    push_cast; ring
  have ha := e252o_sig1 (p + 1 + i)
  have hp0 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpos1 : (0 : ℝ) < ((p - 1) ! : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hpos2 : (0 : ℝ) < (p : ℝ) ^ i := by positivity
  have hfp : (0 : ℝ) < ((p + 1 + i) ! : ℝ) := by exact_mod_cast Nat.factorial_pos _
  rw [div_le_iff₀ hfp, hm]
  push_cast at ha hf ⊢
  have hfi : (p - 1 + 1 + i : ℕ) = p + i := by omega
  rw [hfi] at hf
  push_cast at hf
  have key : (σ 1 (p + 1 + i) : ℝ) * ((p - 1) ! : ℝ) ≤
      ((p + 1 + i : ℝ) / 2 + 1) * (p + 1 + i) * ((p - 1) ! : ℝ) := by
    have : (σ 1 (p + 1 + i) : ℝ) ≤ (p + 1 + i) * ((p + 1 + i) / 2 + 1) := by
      push_cast at ha; linarith
    nlinarith
  refine le_trans key ?_
  rw [div_pow, one_pow, show p - 1 + 1 + i = p + i by omega]
  have hpi : (0 : ℝ) < p + i := by positivity
  have hrhs : (1 / 2 + 3 / (2 * p)) * (1 / (p : ℝ) ^ i) * ((p + 1 + i) * ((p + i) ! : ℝ)) ≥
      (1 / 2 + 3 / (2 * p)) * (1 / (p : ℝ) ^ i) * ((p + 1 + i) * (((p - 1) ! : ℝ) * p ^ i * (p + i))) := by
    gcongr
  refine le_trans ?_ hrhs
  have : (1 / 2 + 3 / (2 * p)) * (1 / (p : ℝ) ^ i) * ((p + 1 + i) * (((p - 1) ! : ℝ) * p ^ i * (p + i)))
      = (1 / 2 + 3 / (2 * p)) * (p + i) * (p + 1 + i) * ((p - 1) ! : ℝ) := by
    field_simp
  rw [this]
  have h5 : ((p + 1 + i : ℝ) / 2 + 1) ≤ (1 / 2 + 3 / (2 * p)) * (p + i) := by
    rw [show (1 / 2 + 3 / (2 * (p : ℝ))) * (p + i) = (p + i) / 2 + 3 * (p + i) / (2 * p) by ring]
    have : (3 : ℝ) / 2 ≤ 3 * (p + i) / (2 * p) := by
      rw [le_div_iff₀ (by positivity)]; have : (0 : ℝ) ≤ i := by positivity
      nlinarith
    linarith
  have h6 : (0 : ℝ) ≤ (p + 1 + i) * ((p - 1) ! : ℝ) := by positivity
  nlinarith

/-- `∑ σ 1 n / n!` is irrational. This is proved in [ErSt74]. -/
@[category research solved, AMS 11]
theorem erdos_252.variants.k_eq_one : Irrational (erdos_252_sum 1) := by
  rintro ⟨r, hr⟩
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (r.den + 11)
  set N := p - 1 with hN
  have hNp : N + 1 = p := by omega
  let f : ℕ → ℝ := fun n => (σ 1 n : ℝ) / (n ! : ℝ)
  have hs : Summable f := e252o_summable1
  have hsplit := (hs.sum_add_tsum_nat_add p).symm
  have hx : erdos_252_sum 1 = ∑' n, f n := rfl
  set T := ∑' j, f (j + p) with hT
  have hs' : Summable (fun j => f (j + p)) := (summable_nat_add_iff p).mpr hs
  have hT2 : T = f p + ∑' i, f (i + 1 + p) := by
    rw [hT, hs'.tsum_eq_zero_add]
    simp only [zero_add]
  have hs'' : Summable (fun i => f (i + 1 + p)) := by
    have := (summable_nat_add_iff 1).mpr hs'
    simpa using this
  have hNf : (0 : ℝ) < N ! := by exact_mod_cast Nat.factorial_pos N
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hpR : (11 : ℝ) ≤ p := by exact_mod_cast (show 11 ≤ p by omega)
  -- first term
  have hfirst : (N ! : ℝ) * f p = (p + 1) / p := by
    simp only [f]
    rw [ArithmeticFunction.sigma_one_apply, Nat.Prime.sum_divisors hp, ← hNp, Nat.factorial_succ]
    push_cast
    have : (N : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  -- tail
  have hterm : ∀ i, (N ! : ℝ) * f (i + 1 + p) ≤ (1 / 2 + 3 / (2 * p)) * (1 / (p : ℝ)) ^ i := by
    intro i
    have := e252o_term1 p i hp.one_lt.le
    simp only [f]
    rw [show i + 1 + p = p + 1 + i by ring]
    calc (N ! : ℝ) * ((σ 1 (p + 1 + i) : ℝ) / ((p + 1 + i) ! : ℝ)) =
        (σ 1 (p + 1 + i) : ℝ) * ((p - 1) ! : ℝ) / ((p + 1 + i) ! : ℝ) := by ring
      _ ≤ _ := this
  have hr1 : (1 / (p : ℝ)) < 1 := by rw [div_lt_one (by positivity)]; linarith
  have hgeo : Summable (fun i : ℕ => (1 / 2 + 3 / (2 * p : ℝ)) * (1 / (p : ℝ)) ^ i) :=
    (summable_geometric_of_lt_one (by positivity) hr1).mul_left _
  have htail_le : (N ! : ℝ) * ∑' i, f (i + 1 + p) ≤ (1 / 2 + 3 / (2 * p : ℝ)) * (1 - 1 / (p : ℝ))⁻¹ := by
    rw [← tsum_mul_left, ← tsum_geometric_of_lt_one (by positivity) hr1, ← tsum_mul_left]
    exact Summable.tsum_le_tsum hterm (hs''.mul_left _) hgeo
  have htail_nn : 0 ≤ (N ! : ℝ) * ∑' i, f (i + 1 + p) :=
    mul_nonneg hNf.le (tsum_nonneg (fun i => by simp only [f]; positivity))
  have hTlt : (N ! : ℝ) * T < 2 := by
    rw [hT2, mul_add, hfirst]
    have h1 : (1 - 1 / (p : ℝ))⁻¹ = p / (p - 1) := by
      rw [show (1 : ℝ) - 1 / p = (p - 1) / p by field_simp, inv_div]
    rw [h1] at htail_le
    have h2 : (1 / 2 + 3 / (2 * p : ℝ)) * (p / (p - 1)) = (p + 3) / (2 * (p - 1)) := by
      field_simp
    rw [h2] at htail_le
    have h3 : (p + 1 : ℝ) / p + (p + 3) / (2 * (p - 1)) < 2 := by
      rw [div_add_div _ _ (by positivity) (by nlinarith), div_lt_iff₀ (by nlinarith)]
      nlinarith
    linarith
  have hTgt : 1 < (N ! : ℝ) * T := by
    rw [hT2, mul_add, hfirst]
    have : (1 : ℝ) < (p + 1) / p := by rw [lt_div_iff₀ (by positivity)]; linarith
    linarith
  -- integrality
  obtain ⟨m1, hm1⟩ : ∃ m : ℤ, (N ! : ℝ) * (r : ℝ) = m := by
    obtain ⟨c, hc⟩ := Nat.dvd_factorial r.den_pos (show r.den ≤ N by omega)
    refine ⟨c * r.num, ?_⟩
    rw [hc, Rat.cast_def]
    push_cast
    field_simp
  obtain ⟨m2, hm2⟩ : ∃ m : ℕ, (N ! : ℝ) * ∑ i ∈ Finset.range p, f i = m := by
    refine ⟨∑ i ∈ Finset.range p, σ 1 i * (N ! / i !), ?_⟩
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
  rw [hz] at hTlt hTgt
  have h1 : (1 : ℤ) < m1 - m2 := by exact_mod_cast hTgt
  have h2 : m1 - m2 < (2 : ℤ) := by exact_mod_cast hTlt
  omega


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
