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
# Erdős Problem 400

*Reference:* [erdosproblems.com/400](https://www.erdosproblems.com/400)
-/

@[expose] public section

open Nat Filter Finset
open scoped Asymptotics Topology

namespace Erdos400

/--
For any $k\geq 2$ let $g_k(n)$ denote the maximum value of $(a_1+\cdots+a_k)-n$
where $a_1,\ldots,a_k$ are integers such that $a_1!\cdots a_k! \mid n!$.
-/
noncomputable def g (k n : ℕ) : ℕ :=
  sSup { ((∑ i, a i) - n) | (a : Fin k → ℕ) (_ : (∏ i, (a i) !) ∣ n !) }

/--
Can one show that $\sum_{n\leq x}g_k(n) \sim c_k x\log x$ for some constant $c_k$?
-/
@[category research open, AMS 11]
theorem erdos_400.parts.i :
    answer(sorry) ↔ ∀ᵉ (k ≥ 2), ∃ c : ℝ,
      (fun x : ℕ ↦ (∑ n ∈ Icc 1 x, (g k n : ℝ))) ~[atTop]
      (fun x : ℕ ↦ c * x * Real.log x) := by
  sorry

/--
Is it true that there is a constant $c_k$ such that for almost all $n < x$ we have
$g_k(n)=c_k\log x+o(\log x)$?
-/
@[category research open, AMS 11]
theorem erdos_400.parts.ii :
    answer(sorry) ↔ ∀ᵉ (k ≥ 2), ∃ c : ℝ, ∀ ε > 0,
      Tendsto (fun x : ℕ ↦
        (((Icc 1 x).filter (fun n ↦
          |(g k n : ℝ) - c * Real.log x| ≤ ε * Real.log x)).card : ℝ) / x)
        atTop (𝓝 1) := by
  sorry

open Nat in
lemma e400_s2_le (a : ℕ) : (Nat.digits 2 a).sum ≤ Nat.log 2 a + 1 := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  · have h := List.sum_le_card_nsmul (Nat.digits 2 a) 1
      (fun x hx => Nat.lt_succ_iff.mp (Nat.digits_lt_base (by norm_num) hx))
    rw [Nat.length_digits 2 a (by norm_num) ha.ne'] at h
    simpa using h

lemma e400_v2 (a : ℕ) : padicValNat 2 a.factorial + (Nat.digits 2 a).sum = a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := sub_one_mul_padicValNat_factorial (p := 2) a
  have hs := Nat.digit_sum_le 2 a
  simp only [Nat.add_one_sub_one, one_mul] at h
  omega

lemma e400_log_le {a n : ℕ} (h : a.factorial ∣ n.factorial) : Nat.log 2 a ≤ Nat.log 2 n := by
  have hle : a.factorial ≤ n.factorial := Nat.le_of_dvd (Nat.factorial_pos n) h
  rcases Nat.lt_or_ge a 2 with ha | ha
  · interval_cases a <;> simp
  · apply Nat.log_mono_right
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exfalso
      have : 2 ≤ a.factorial := by
        calc 2 = (2 : ℕ).factorial := rfl
          _ ≤ a.factorial := Nat.factorial_le ha
      simp at hle; omega
    · by_contra hna
      push Not at hna
      have := (Nat.factorial_lt hn).mpr hna
      omega

lemma e400_key {k n : ℕ} (a : Fin k → ℕ) (h : (∏ i, (a i).factorial) ∣ n.factorial) :
    ∑ i, a i ≤ n + k * (Nat.log 2 n + 1) := by
  have hne : ∀ i ∈ (Finset.univ : Finset (Fin k)), (a i).factorial ≠ 0 :=
    fun i _ => (Nat.factorial_pos _).ne'
  have hfac := (Nat.factorization_le_iff_dvd (Finset.prod_ne_zero_iff.mpr hne)
    (Nat.factorial_pos n).ne').mpr h 2
  rw [Nat.factorization_prod hne, Finsupp.coe_finsetSum, Finset.sum_apply] at hfac
  simp only [Nat.factorization_def _ Nat.prime_two] at hfac
  have hv := e400_v2 n
  have hsum : ∑ i, a i = ∑ i, padicValNat 2 (a i).factorial + ∑ i, (Nat.digits 2 (a i)).sum := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => (e400_v2 (a i)).symm)
  have hs : ∑ i, (Nat.digits 2 (a i)).sum ≤ k * (Nat.log 2 n + 1) := by
    calc ∑ i, (Nat.digits 2 (a i)).sum ≤ ∑ _i : Fin k, (Nat.log 2 n + 1) := by
          refine Finset.sum_le_sum (fun i _ => (e400_s2_le (a i)).trans ?_)
          have := e400_log_le ((Finset.dvd_prod_of_mem (fun j => (a j).factorial)
            (Finset.mem_univ i)).trans h)
          omega
      _ = k * (Nat.log 2 n + 1) := by simp
  omega

open Nat in
lemma e400_g_le (k n : ℕ) : g k n ≤ k * (Nat.log 2 n + 1) := by
  apply csSup_le
  · exact ⟨_, fun _ => 0, by simp, rfl⟩
  · rintro m ⟨a, ha, rfl⟩
    have := e400_key a ha
    omega

/--
Erdős and Graham write that it is easy to show that $g_k(n) \ll_k \log n$ always, but the best
possible constant is unknown.
-/
@[category research solved, AMS 11]
theorem erdos_400.variants.upper_bound (k : ℕ) (hk : k ≥ 2) :
    (fun n : ℕ ↦ (g k n : ℝ)) ≪ (fun n : ℕ ↦ Real.log (n : ℝ)) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine Asymptotics.IsBigO.of_bound (2 * k / Real.log 2) ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg hlogn]
  have hL : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := by
    have h := Nat.pow_log_le_self 2 (by omega : n ≠ 0)
    have h' : ((2 ^ Nat.log 2 n : ℕ) : ℝ) ≤ n := by exact_mod_cast h
    have := Real.log_le_log (by positivity) h'
    rwa [Nat.cast_pow, Real.log_pow] at this
  have hL1 : 1 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by simpa using hn)
  have hL1' : (1 : ℝ) ≤ Nat.log 2 n := by exact_mod_cast hL1
  have hg : (g k n : ℝ) ≤ k * (Nat.log 2 n + 1) := by exact_mod_cast e400_g_le k n
  have hk0 : (0 : ℝ) ≤ k := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
  calc (g k n : ℝ) * Real.log 2 ≤ k * (Nat.log 2 n + 1) * Real.log 2 :=
        mul_le_mul_of_nonneg_right hg hl2.le
    _ ≤ k * (2 * Nat.log 2 n) * Real.log 2 := by gcongr; linarith
    _ = 2 * k * ((Nat.log 2 n : ℝ) * Real.log 2) := by ring
    _ ≤ 2 * k * Real.log n := by gcongr


/-- For $k \ge 2$, $g_k(n) > 0$. We show this by choosing $a = (n, 1, 0, \ldots, 0)$. -/
@[category test, AMS 11]
theorem erdos_400.variants.g_pos (k n : ℕ) (h: k ≥ 2) : 0 < g k n := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
  simp only [g]
  -- Witness: a(0) = n, a(1) = 1, a(i) = 0 for i ≥ 2
  set a : Fin (k' + 2) → ℕ := fun i =>
    if (i : ℕ) = 0 then n else if (i : ℕ) = 1 then 1 else 0 with ha_def
  have h_prod : ∏ i : Fin (k' + 2), (a i)! = n ! := by
    rw [Fin.prod_univ_succ]; simp [ha_def]
    rw [Fin.prod_univ_succ]; simp
  have h_sum : ∑ i : Fin (k' + 2), a i = n + 1 := by
    rw [Fin.sum_univ_succ]; simp [ha_def]
  -- 1 is in the set
  have hmem : 1 ∈ {(∑ i, b i) - n | (b : Fin (k' + 2) → ℕ) (_ : ∏ i, (b i)! ∣ n !)} :=
    ⟨a, h_prod ▸ dvd_refl n !, by omega⟩
  -- The set is bounded above by (k'+2) * n!
  have hbdd : BddAbove {(∑ i, b i) - n | (b : Fin (k' + 2) → ℕ) (_ : ∏ i, (b i)! ∣ n !)} := by
    refine ⟨(k' + 2) * n !, ?_⟩
    rintro x ⟨b, hb, rfl⟩
    calc (∑ i, b i) - n
        ≤ ∑ i, b i := Nat.sub_le _ _
      _ ≤ ∑ i : Fin (k' + 2), (b i)! :=
          Finset.sum_le_sum fun i _ => Nat.self_le_factorial _
      _ ≤ Finset.univ.card • n ! := by
          apply Finset.sum_le_card_nsmul; intro i _
          exact le_trans (Finset.single_le_prod' (fun j _ =>
            Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _))
            (Finset.mem_univ i)) (Nat.le_of_dvd (Nat.factorial_pos n) hb)
      _ = (k' + 2) * n ! := by simp [smul_eq_mul]
  exact Nat.lt_of_lt_of_le Nat.one_pos (le_csSup hbdd hmem)

end Erdos400
