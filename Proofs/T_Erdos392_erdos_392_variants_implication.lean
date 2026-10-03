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
# Erdős Problem 392

*Reference:* [erdosproblems.com/392](https://www.erdosproblems.com/392)
-/

@[expose] public section

open Filter

open scoped Nat

namespace Erdos392

/--
Let $A(n)$ denote the least value of $t$ such that
$$
  n! = a_1 \cdots a_t
$$
with $a_1 \leq \cdots \leq a_t\leq n^2$. Then
$$
  A(n) = \frac{n}{2} - \frac{n}{2\log n} + o\left(\frac{n}{\log n}\right).
$$
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/d82a35ecc798ada27f82a88b559f25b753f63a73/PrimeNumberTheoremAnd/IEANTN/Erdos392.lean"]
theorem erdos_392 (A : ℕ → ℕ) (h : ∀ n > 0,
    IsLeast { t + 1 | (t) (_ : ∃ a : Fin (t + 1) → ℕ, (n)! = ∏ i, a i ∧
      Monotone a ∧ a (Fin.last t) ≤ n ^ 2) } (A n)) :
    ((fun (n : ℕ) => (A n - n / 2 + n / (2 * Real.log n) : ℝ)) =o[atTop] fun n => n / Real.log n)
  := by
  sorry

/--
If we change the condition to $a_t \leq n$ it can be shown that
$$
  A(n) = n - \frac{n}{\log n} + o\left(\frac{n}{\log n}\right)
$$
-/
@[category research solved, AMS 11]
theorem erdos_392.variants.lower (A : ℕ → ℕ)
    (hA : ∀ n > 0, IsLeast
      { t + 1 | (t) (_ : ∃ a : Fin (t + 1) → ℕ, (n)! = ∏ i, a i ∧
        Monotone a ∧ a (Fin.last t) ≤ n) } (A n)) :
    (fun (n : ℕ) => (A n - n + n / Real.log n : ℝ)) =o[atTop] fun n => n / Real.log n := by
  sorry

open Finset in
lemma e392_pair_prod (g : ℕ → ℕ) : ∀ k, ∏ i ∈ range k, (g (2 * i) * g (2 * i + 1)) = ∏ j ∈ range (2 * k), g j := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [prod_range_succ, ih, show 2 * (k + 1) = 2 * k + 1 + 1 by ring, prod_range_succ, prod_range_succ]
    ring

open Finset in
/-- Pairing: a monotone factorisation of `n!` with `m ≥ 1` factors `≤ n` gives one with `(m+1)/2`
factors `≤ n²`. -/
lemma e392_pair (n m : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (a : Fin m → ℕ) (hprod : n ! = ∏ i, a i)
    (hmono : Monotone a) (hlast : a ⟨m - 1, by omega⟩ ≤ n) :
    ∃ t, t + 1 = (m + 1) / 2 ∧ ∃ b : Fin (t + 1) → ℕ,
      n ! = ∏ i, b i ∧ Monotone b ∧ b (Fin.last t) ≤ n ^ 2 := by
  have hpos : ∀ i, 1 ≤ a i := by
    intro i
    by_contra h
    push Not at h
    have : a i = 0 := by omega
    have h0 : ∏ j, a j = 0 := Finset.prod_eq_zero (Finset.mem_univ i) this
    rw [← hprod] at h0
    exact (Nat.factorial_pos n).ne' h0
  have hle : ∀ i, a i ≤ n := fun i => (hmono (show i ≤ ⟨m - 1, by omega⟩ from
    Fin.le_iff_val_le_val.mpr (by have := i.isLt; simp; omega))).trans hlast
  set f : ℕ → ℕ := fun j => if h : j < m then a ⟨j, h⟩ else 1 with hf
  set s := m % 2 with hs
  set a' : ℕ → ℕ := fun j => if s = 1 then (if j = 0 then 1 else f (j - 1)) else f j with ha'
  set L := m + s with hL
  have hLeven : L = 2 * ((m + 1) / 2) := by omega
  -- basic facts on f and a'
  have hf1 : ∀ j, 1 ≤ f j := by intro j; simp only [hf]; split_ifs <;> simp [hpos]
  have hfn : ∀ j, f j ≤ n := by intro j; simp only [hf]; split_ifs <;> simp [hle, hn]
  have hfmono : ∀ j₁ j₂, j₁ ≤ j₂ → j₂ < m → f j₁ ≤ f j₂ := by
    intro j₁ j₂ h12 h2
    simp only [hf, dif_pos h2, dif_pos (lt_of_le_of_lt h12 h2)]
    exact hmono (Fin.le_iff_val_le_val.mpr h12)
  have ha'1 : ∀ j, 1 ≤ a' j := by intro j; simp only [ha']; split_ifs <;> simp [hf1]
  have ha'n : ∀ j, a' j ≤ n := by intro j; simp only [ha']; split_ifs <;> simp [hfn, hn]
  have ha'mono : ∀ j₁ j₂, j₁ ≤ j₂ → j₂ < L → a' j₁ ≤ a' j₂ := by
    intro j₁ j₂ h12 h2
    simp only [ha']
    split_ifs with h1 h3 h4 h4
    · exact le_rfl
    · exact hf1 _
    · omega
    · exact hfmono _ _ (by omega) (by omega)
    · exact hfmono _ _ h12 (by omega)
  have hprodL : ∏ j ∈ range L, a' j = n ! := by
    have hfprod : ∏ j ∈ range m, f j = n ! := by
      rw [hprod, ← Fin.prod_univ_eq_prod_range f m]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      simp [hf, i.isLt]
    rcases Nat.mod_two_eq_zero_or_one m with h0 | h1
    · have hs0 : s = 0 := h0
      rw [hL, hs0, add_zero, ← hfprod]
      refine Finset.prod_congr rfl (fun j _ => ?_)
      simp [ha', hs0]
    · have hs1 : s = 1 := h1
      rw [hL, hs1, prod_range_succ', ← hfprod]
      simp only [ha', hs1, if_true, if_pos rfl, mul_one]
      refine Finset.prod_congr rfl (fun j _ => ?_)
      simp
  obtain ⟨t, ht⟩ : ∃ t, t + 1 = (m + 1) / 2 := ⟨(m + 1) / 2 - 1, by omega⟩
  refine ⟨t, ht, fun i => a' (2 * i) * a' (2 * i + 1), ?_, ?_, ?_⟩
  · rw [← hprodL, hLeven, ← ht, ← e392_pair_prod a' (t + 1), ← Fin.prod_univ_eq_prod_range]
  · intro i i' hii
    have := Fin.le_iff_val_le_val.mp hii
    have hi' := i'.isLt
    exact Nat.mul_le_mul (ha'mono _ _ (by omega) (by omega)) (ha'mono _ _ (by omega) (by omega))
  · simp only [Fin.val_last]
    rw [sq]
    exact Nat.mul_le_mul (ha'n _) (ha'n _)

open Finset in
lemma e392_div_log_tendsto : Tendsto (fun n : ℕ => (n : ℝ) / Real.log n) atTop atTop := by
  have hs : Tendsto (fun n : ℕ => Real.sqrt n / 2) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const (by norm_num)
  refine tendsto_atTop_mono' atTop ?_ hs
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 < Real.log n := Real.log_pos (by linarith)
  have hle : Real.log n ≤ 2 * Real.sqrt n := by
    have := Real.log_le_rpow_div (x := (n : ℝ)) (ε := 1 / 2) (by positivity) (by norm_num)
    rw [← Real.sqrt_eq_rpow] at this; linarith
  have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (by positivity)
  have hsp : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
  rw [le_div_iff₀ hlog]
  nlinarith

open Finset in
lemma e392_stirling (n : ℕ) (hn : 1 ≤ n) : (n : ℝ) * Real.log n - n ≤ Real.log (n ! : ℝ) := by
  have h := Stirling.le_factorial_stirling n
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * n) := by
    rw [Real.one_le_sqrt]; nlinarith [Real.pi_gt_three]
  have hpow : ((n : ℝ) / Real.exp 1) ^ n ≤ (n ! : ℝ) := by
    have : 0 ≤ ((n : ℝ) / Real.exp 1) ^ n := by positivity
    nlinarith
  have hpos : 0 < ((n : ℝ) / Real.exp 1) ^ n := by positivity
  have := Real.log_le_log hpos hpow
  rw [Real.log_pow, Real.log_div (by positivity) (by positivity), Real.log_exp] at this
  linarith

/--
Cambie has observed that a positive answer follows from the result above with $a_t \leq n$, simply
by pairing variables together, e.g. taking $a'_i = a_{2i-1}a_{2i}$ (and the lower bound follows from
Stirling's approximation).
-/
@[category research solved, AMS 11]
theorem erdos_392.variants.implication (h : type_of% erdos_392.variants.lower) :
    type_of% erdos_392 := by
  intro A2 hA2
  set S1 : ℕ → Set ℕ := fun n => { t + 1 | (t) (_ : ∃ a : Fin (t + 1) → ℕ, (n)! = ∏ i, a i ∧
        Monotone a ∧ a (Fin.last t) ≤ n) } with hS1
  have hne : ∀ n > 0, (S1 n).Nonempty := by
    intro n hn
    obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 := ⟨n - 1, by omega⟩
    refine ⟨t + 1, t, ⟨fun i => i.val + 1, ?_, ?_, ?_⟩, rfl⟩
    · rw [Fin.prod_univ_eq_prod_range (fun i => i + 1), Finset.prod_range_add_one_eq_factorial]
    · intro i j hij; simp only; have := Fin.le_iff_val_le_val.mp hij; omega
    · simp
  set A1 : ℕ → ℕ := fun n => sInf (S1 n)
  have hA1 : ∀ n > 0, IsLeast (S1 n) (A1 n) :=
    fun n hn => ⟨Nat.sInf_mem (hne n hn), fun y hy => Nat.sInf_le hy⟩
  have h1 := h A1 hA1
  -- upper bound via pairing
  have hup : ∀ n ≥ 1, 2 * A2 n ≤ A1 n + 1 := by
    intro n hn
    obtain ⟨t, ⟨a, hprod, hmono, hlast⟩, ht⟩ := (hA1 n hn).1
    obtain ⟨t', ht', b, hbprod, hbmono, hblast⟩ :=
      e392_pair n (t + 1) (by omega) hn a hprod hmono (by simpa [Fin.last] using hlast)
    have := (hA2 n hn).2 ⟨t', ⟨b, hbprod, hbmono, hblast⟩, rfl⟩
    have hA1t : A1 n = t + 1 := ht.symm
    omega
  -- lower bound via Stirling
  have hlow : ∀ n : ℕ, n ≥ 2 → (n : ℝ) / 2 - n / (2 * Real.log n) ≤ A2 n := by
    intro n hn
    obtain ⟨t, ⟨b, hprod, hmono, hlast⟩, ht⟩ := (hA2 n (by omega)).1
    have hble : ∀ i, b i ≤ n ^ 2 := fun i => (hmono (Fin.le_last i)).trans hlast
    have hfac : n ! ≤ (n ^ 2) ^ (t + 1) := by
      rw [hprod]
      calc ∏ i, b i ≤ (n ^ 2) ^ (Finset.univ : Finset (Fin (t + 1))).card :=
            Finset.prod_le_pow_card _ _ _ (fun i _ => hble i)
        _ = (n ^ 2) ^ (t + 1) := by simp
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hlog : 0 < Real.log n := Real.log_pos (by linarith)
    have hfacR : Real.log (n ! : ℝ) ≤ (t + 1) * (2 * Real.log n) := by
      have : ((n ! : ℕ) : ℝ) ≤ (((n ^ 2) ^ (t + 1) : ℕ) : ℝ) := by exact_mod_cast hfac
      have h2 := Real.log_le_log (by positivity) this
      push_cast at h2
      rw [Real.log_pow, Real.log_pow] at h2
      push_cast at h2
      linarith
    have hst := e392_stirling n (by omega)
    have hA2t : (A2 n : ℝ) = t + 1 := by exact_mod_cast ht.symm
    rw [hA2t]
    rw [sub_le_iff_le_add, div_le_iff₀ (by positivity)]
    have : (n : ℝ) / (2 * Real.log n) * (2 * Real.log n) = n := by field_simp
    nlinarith
  -- asymptotics
  set g : ℕ → ℝ := fun n => (n : ℝ) / Real.log n
  set E1 : ℕ → ℝ := fun n => (A1 n - n + n / Real.log n : ℝ)
  have hconst : (fun _ : ℕ => (1 / 2 : ℝ)) =o[atTop] g :=
    Asymptotics.isLittleO_const_left.mpr (Or.inr (tendsto_norm_atTop_atTop.comp e392_div_log_tendsto))
  have hh : (fun n => ‖E1 n‖ / 2 + 1 / 2) =o[atTop] g :=
    ((h1.norm_left).const_mul_left (1 / 2) |>.congr_left (fun n => by ring)).add hconst
  refine Asymptotics.IsBigO.trans_isLittleO ?_ hh
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 < Real.log n := Real.log_pos (by linarith)
  have hl := hlow n hn
  have hu : (2 * A2 n : ℝ) ≤ A1 n + 1 := by exact_mod_cast hup n (by omega)
  have hE1 : |E1 n| ≥ E1 n := le_abs_self _
  have hsplit : (n : ℝ) / (2 * Real.log n) = (n / Real.log n) / 2 := by field_simp
  rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, abs_of_nonneg (by linarith),
    abs_of_nonneg (by positivity)]
  simp only [E1] at hE1 ⊢
  rw [hsplit] at hl ⊢
  simp only [Real.norm_eq_abs] at *
  linarith

end Erdos392
