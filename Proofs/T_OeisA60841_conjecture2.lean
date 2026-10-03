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
# Numerator of $1/\det(M)$ for $M[i,j] = 1/\operatorname{lcm}(i,j)$

Numerator of $1/\det(M)$ where $M$ is the $n \times n$ matrix with
$M[i,j] = 1/\operatorname{lcm}(i,j)$.

*References:*
- [A060841](https://oeis.org/A060841)
- T. Adamczewski, "OEIS Open: How many conjectures can language models turn into theorems?",
  [arXiv:2608.11941](https://arxiv.org/abs/2608.11941) [cs.AI], 2026.
-/

@[expose] public section

namespace OeisA60841

/-- The $n \times n$ matrix with entry $(i,j)$ equal to
$1/\operatorname{lcm}(i+1, j+1)$ over $\mathbb{Q}$. -/
def lcmMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i j : Fin n ↦ 1 / ((Nat.lcm (i.val + 1) (j.val + 1) : ℚ))

/-- Numerator of $1/\det(M)$ where $M$ is the $n \times n$ matrix with
$M[i,j] = 1/\operatorname{lcm}(i+1,j+1)$. -/
def a (n : ℕ) : ℤ :=
  ((lcmMatrix n).det)⁻¹.num

@[category test, AMS 11 15]
theorem a_1 : a 1 = 1 := by
  decide +kernel

@[category test, AMS 11 15]
theorem a_2 : a 2 = 4 := by
  decide +kernel

@[category test, AMS 11 15]
theorem a_3 : a 3 = 18 := by
  decide +kernel

@[category test, AMS 11 15]
theorem a_4 : a 4 = 144 := by
  decide +kernel

@[category test, AMS 11 15]
theorem a_5 : a 5 = 900 := by
  decide +kernel

/-- The exceptional values of $n$ where $1/\det(M)$ is conjectured to be an integer. -/
def integerDetN : Set ℕ :=
  Set.Icc 1 34 ∪ {36, 38}

/--
"Conjecture: $1/\det(M)$ is an integer only for n: 1 to 34, 36 and 38." - _Robert G. Wilson v_,
Aug 02 2015
-/
@[category research open, AMS 11 15]
theorem conjecture1 :
    ∀ n : ℕ, 1 ≤ n → (((lcmMatrix n).det)⁻¹.den = 1 ↔ n ∈ integerDetN) := by
  sorry

open Finset in
/-- Divisor-incidence matrix. -/
def a608E (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i k : Fin n => if (k.val + 1) ∣ (i.val + 1) then 1 else 0

open Finset in
lemma a608_E_det (n : ℕ) : (a608E n).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · simp [a608E]
  · intro i k hik
    simp only [a608E, Matrix.of_apply]
    rw [if_neg]
    intro hdvd
    have := Nat.le_of_dvd (Nat.succ_pos _) hdvd
    have hik' : i < k := hik
    have : i.val < k.val := hik'
    omega

open Finset in
lemma a608_sum_dvd (n a b : ℕ) (ha : 1 ≤ a) (han : a ≤ n) (hb : 1 ≤ b) :
    ∑ k : Fin n, (if (k.val + 1) ∣ a ∧ (k.val + 1) ∣ b then (Nat.totient (k.val + 1) : ℚ) else 0)
      = Nat.gcd a b := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if (k + 1) ∣ a ∧ (k + 1) ∣ b then
    (Nat.totient (k + 1) : ℚ) else 0) n, ← Finset.sum_filter]
  have hg : Nat.gcd a b ≠ 0 := Nat.gcd_ne_zero_left (by omega)
  have : ((range n).filter fun k => (k + 1) ∣ a ∧ (k + 1) ∣ b).map (addRightEmbedding 1)
      = (Nat.gcd a b).divisors := by
    ext d
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_range, addRightEmbedding_apply,
      Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨k, ⟨hk, h1, h2⟩, rfl⟩
      exact ⟨⟨h1, h2⟩, hg⟩
    · rintro ⟨⟨h1, h2⟩, -⟩
      have hd : 1 ≤ d := Nat.pos_of_dvd_of_pos h1 (by omega)
      refine ⟨d - 1, ⟨?_, ?_, ?_⟩, by omega⟩
      · have := Nat.le_of_dvd (by omega) h1; omega
      · rwa [Nat.sub_add_cancel hd]
      · rwa [Nat.sub_add_cancel hd]
  have hsum := congrArg (fun s => ∑ d ∈ s, (Nat.totient d : ℚ)) this
  simp only [Finset.sum_map, addRightEmbedding_apply] at hsum
  rw [hsum]
  exact_mod_cast Nat.sum_totient (Nat.gcd a b)

open Finset in
lemma a608_G (n : ℕ) (i j : Fin n) :
    (a608E n * Matrix.diagonal (fun k : Fin n => (Nat.totient (k.val + 1) : ℚ)) * (a608E n).transpose) i j
      = Nat.gcd (i.val + 1) (j.val + 1) := by
  rw [← a608_sum_dvd n (i.val + 1) (j.val + 1) (by omega) i.isLt (by omega), Matrix.mul_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.mul_diagonal, Matrix.transpose_apply]
  simp only [a608E, Matrix.of_apply]
  split_ifs <;> simp_all

open Finset in
lemma a608_factor (n : ℕ) :
    lcmMatrix n = Matrix.diagonal (fun i : Fin n => 1 / ((i.val + 1 : ℕ) : ℚ)) *
      (a608E n * Matrix.diagonal (fun k : Fin n => (Nat.totient (k.val + 1) : ℚ)) * (a608E n).transpose) *
      Matrix.diagonal (fun j : Fin n => 1 / ((j.val + 1 : ℕ) : ℚ)) := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, a608_G]
  simp only [lcmMatrix, Matrix.of_apply]
  have hl := Nat.gcd_mul_lcm (i.val + 1) (j.val + 1)
  have hl' : ((Nat.gcd (i.val + 1) (j.val + 1) : ℕ) : ℚ) * (Nat.lcm (i.val + 1) (j.val + 1) : ℕ)
      = ((i.val + 1 : ℕ) : ℚ) * ((j.val + 1 : ℕ) : ℚ) := by exact_mod_cast hl
  have hlcm : ((Nat.lcm (i.val + 1) (j.val + 1) : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.lcm_ne_zero (by omega) (by omega)
  have hi : ((i.val + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : i.val + 1 ≠ 0)
  have hj : ((j.val + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : j.val + 1 ≠ 0)
  have hg : ((Nat.gcd (i.val + 1) (j.val + 1) : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.gcd_ne_zero_left (by omega)
  field_simp
  linear_combination (-1 : ℚ) * hl'

open Finset in
lemma a608_det (n : ℕ) : (lcmMatrix n).det =
    ∏ i : Fin n, ((Nat.totient (i.val + 1) : ℚ) / ((i.val + 1 : ℕ) : ℚ) ^ 2) := by
  rw [a608_factor, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, a608_E_det, Matrix.det_diagonal, Matrix.det_diagonal]
  simp only [one_mul, mul_one]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  ring

open Finset in
/-- Trial division: least divisor `≥ d` of `n` (or `n`), with fuel. -/
def a608mf : ℕ → ℕ → ℕ → ℕ
  | 0, _, n => n
  | f + 1, d, n => if n % d = 0 then d else if n < d * d then n else a608mf f (d + 1) n

open Finset in
lemma a608_mf_spec (n : ℕ) (hn : 2 ≤ n) : ∀ f d, 2 ≤ d → d ≤ n → n ≤ d + f →
    (∀ e, 2 ≤ e → e < d → ¬ e ∣ n) → (a608mf f d n).Prime ∧ a608mf f d n ∣ n := by
  have key : ∀ p, p ∣ n → 2 ≤ p → (∀ e, 2 ≤ e → e < p → ¬ e ∣ n) → p.Prime ∧ p ∣ n := by
    intro p hp hp2 hmin
    exact ⟨Nat.prime_def_lt'.mpr ⟨hp2, fun m hm2 hmp hmd => hmin m hm2 hmp (hmd.trans hp)⟩, hp⟩
  intro f
  induction f with
  | zero =>
    intro d hd2 hdn hnd hmin
    simp only [a608mf]
    have : d = n := by omega
    subst this
    exact key d dvd_rfl hd2 hmin
  | succ f ih =>
    intro d hd2 hdn hnd hmin
    simp only [a608mf]
    split_ifs with h1 h2
    · exact key d (Nat.dvd_of_mod_eq_zero h1) hd2 hmin
    · refine key n dvd_rfl hn fun e he2 hen hdvd => ?_
      -- a proper divisor `e` gives a cofactor `< d`
      obtain ⟨c, rfl⟩ := hdvd
      have hc2 : 2 ≤ c := by
        rcases Nat.lt_or_ge c 2 with hc | hc
        · interval_cases c <;> omega
        · exact hc
      by_cases hed : e < d
      · exact hmin e he2 hed (Dvd.intro c rfl)
      · have hcd : c < d := by nlinarith
        exact hmin c hc2 hcd (Dvd.intro_left e rfl)
    · have hdn' : d ≠ n := by rintro rfl; simp at h1
      refine ih (d + 1) (by omega) (by omega) (by omega) fun e he2 hed => ?_
      rcases Nat.lt_or_ge e d with h | h
      · exact hmin e he2 h
      · have : e = d := by omega
        subst this; exact fun hdvd => h1 (Nat.mod_eq_zero_of_dvd hdvd)

open Finset in
/-- Totient via trial division, with fuel. -/
def a608tf : ℕ → ℕ → ℕ
  | 0, _ => 1
  | f + 1, n => if n ≤ 1 then 1 else
      (if (n / a608mf n 2 n) % (a608mf n 2 n) = 0 then a608mf n 2 n else a608mf n 2 n - 1) *
        a608tf f (n / a608mf n 2 n)

open Finset in
lemma a608_mf (n : ℕ) (hn : 2 ≤ n) : (a608mf n 2 n).Prime ∧ a608mf n 2 n ∣ n :=
  a608_mf_spec n hn n 2 le_rfl hn (by omega) (fun e he2 he => by omega)

open Finset in
lemma a608_tf : ∀ f n, 1 ≤ n → n ≤ f → a608tf f n = Nat.totient n := by
  intro f
  induction f with
  | zero => intro n h1 h2; omega
  | succ f ih =>
    intro n h1 h2
    simp only [a608tf]
    split_ifs with hn1 hm
    · have : n = 1 := by omega
      subst this; simp
    · obtain ⟨hp, hpn⟩ := a608_mf n (by omega)
      set p := a608mf n 2 n
      obtain ⟨m, hm'⟩ := hpn
      have hp2 := hp.two_le
      have hm1 : 1 ≤ m := by rcases Nat.eq_zero_or_pos m with h | h <;> [simp [h] at hm'; omega]; omega
      have hdiv : n / p = m := by rw [hm']; exact Nat.mul_div_cancel_left m (by omega)
      rw [hdiv] at hm ⊢
      have hmn : m < n := by rw [hm']; nlinarith
      rw [ih m hm1 (by omega), hm', Nat.totient_mul_of_prime_of_dvd hp (Nat.dvd_of_mod_eq_zero hm)]
    · obtain ⟨hp, hpn⟩ := a608_mf n (by omega)
      set p := a608mf n 2 n
      obtain ⟨m, hm'⟩ := hpn
      have hp2 := hp.two_le
      have hm1 : 1 ≤ m := by rcases Nat.eq_zero_or_pos m with h | h <;> [simp [h] at hm'; omega]; omega
      have hdiv : n / p = m := by rw [hm']; exact Nat.mul_div_cancel_left m (by omega)
      rw [hdiv] at hm ⊢
      have hmn : m < n := by rw [hm']; nlinarith
      rw [ih m hm1 (by omega), hm', Nat.totient_mul_of_prime_of_not_dvd hp
        (fun h => hm (Nat.mod_eq_zero_of_dvd h))]

open Finset in
/-- 3-adic valuation with fuel. -/
def a608v3 : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, n => if n ≠ 0 ∧ n % 3 = 0 then a608v3 f (n / 3) + 1 else 0

open Finset in
lemma a608_v3 : ∀ f n, n ≤ f → a608v3 f n = padicValNat 3 n := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro f
  induction f with
  | zero => intro n h; have : n = 0 := by omega
            subst this; simp [a608v3]
  | succ f ih =>
    intro n h
    simp only [a608v3]
    split_ifs with hn
    · have h3 : 3 ∣ n := Nat.dvd_of_mod_eq_zero hn.2
      rw [ih (n / 3) (by omega), padicValNat.div h3]
      have := one_le_padicValNat_of_dvd hn.1 h3
      omega
    · rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0; simp
      · exact (padicValNat.eq_zero_of_not_dvd fun h3 => hn ⟨h0.ne', Nat.mod_eq_zero_of_dvd h3⟩).symm

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 100000 in
open Finset in
lemma a608_c0 : ∑ k ∈ Finset.Ico 0 452,
    ((2 * a608v3 (k + 1) (k + 1) : ℤ) - a608v3 (a608tf (k + 1) (k + 1)) (a608tf (k + 1) (k + 1))) = 69 := by
  decide

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 100000 in
open Finset in
lemma a608_c1 : ∑ k ∈ Finset.Ico 452 904,
    ((2 * a608v3 (k + 1) (k + 1) : ℤ) - a608v3 (a608tf (k + 1) (k + 1)) (a608tf (k + 1) (k + 1))) = 0 := by
  decide

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 100000 in
open Finset in
lemma a608_c2 : ∑ k ∈ Finset.Ico 904 1356,
    ((2 * a608v3 (k + 1) (k + 1) : ℤ) - a608v3 (a608tf (k + 1) (k + 1)) (a608tf (k + 1) (k + 1))) = -24 := by
  decide

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 100000 in
open Finset in
lemma a608_c3 : ∑ k ∈ Finset.Ico 1356 1807,
    ((2 * a608v3 (k + 1) (k + 1) : ℤ) - a608v3 (a608tf (k + 1) (k + 1)) (a608tf (k + 1) (k + 1))) = -46 := by
  decide

open Finset in
lemma a608_sum : ∑ k ∈ Finset.range 1807,
    ((2 * a608v3 (k + 1) (k + 1) : ℤ) - a608v3 (a608tf (k + 1) (k + 1)) (a608tf (k + 1) (k + 1))) = -1 := by
  rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (by norm_num : 0 ≤ 1356) (by norm_num : 1356 ≤ 1807),
    ← Finset.sum_Ico_consecutive _ (by norm_num : 0 ≤ 904) (by norm_num : 904 ≤ 1356),
    ← Finset.sum_Ico_consecutive _ (by norm_num : 0 ≤ 452) (by norm_num : 452 ≤ 904),
    a608_c0, a608_c1, a608_c2, a608_c3]
  norm_num

open Finset in
lemma a608_padicValRat_prod {ι : Type*} (s : Finset ι) (f : ι → ℚ) (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValRat 3 (∏ i ∈ s, f i) = ∑ i ∈ s, padicValRat 3 (f i) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hfa : f a ≠ 0 := hf a (Finset.mem_insert_self a s)
    have hfs : (∏ i ∈ s, f i) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [padicValRat.mul hfa hfs, ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

open Finset in
lemma a608_val (n : ℕ) : padicValRat 3 ((lcmMatrix n).det)⁻¹ = ∑ k ∈ Finset.range n,
    ((2 * a608v3 (k + 1) (k + 1) : ℤ) - a608v3 (a608tf (k + 1) (k + 1)) (a608tf (k + 1) (k + 1))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq : ((lcmMatrix n).det)⁻¹ =
      ∏ i ∈ Finset.range n, (((i + 1 : ℕ) : ℚ) ^ 2 / (Nat.totient (i + 1) : ℚ)) := by
    simp only [a608_det, ← Finset.prod_inv_distrib, inv_div]
    exact Fin.prod_univ_eq_prod_range (fun i => (((i + 1 : ℕ) : ℚ) ^ 2 / (Nat.totient (i + 1) : ℚ))) n
  have hne : ∀ i ∈ Finset.range n, (((i + 1 : ℕ) : ℚ) ^ 2 / (Nat.totient (i + 1) : ℚ)) ≠ 0 := by
    intro i _
    have h1 : ((i + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : i + 1 ≠ 0)
    have h2 : (Nat.totient (i + 1) : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr (by omega)).ne'
    exact div_ne_zero (pow_ne_zero _ h1) h2
  rw [hq, a608_padicValRat_prod _ _ hne]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : ((i + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : i + 1 ≠ 0)
  have h2 : (Nat.totient (i + 1) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (by omega)).ne'
  rw [padicValRat.div (pow_ne_zero _ h1) h2, padicValRat.pow, padicValRat.of_nat,
    padicValRat.of_nat, a608_tf (i + 1) (i + 1) (by omega) le_rfl,
    a608_v3 (i + 1) (i + 1) le_rfl,
    a608_v3 (Nat.totient (i + 1)) (Nat.totient (i + 1)) le_rfl]
  push_cast; ring

open Finset in
theorem a608_main : ¬ ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, ((lcmMatrix n).det)⁻¹.den = 2 ^ k := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro h
  obtain ⟨k, hk⟩ := h 1807 (by norm_num)
  have hval := a608_val 1807
  rw [a608_sum] at hval
  generalize ((lcmMatrix 1807).det)⁻¹ = q at hval hk
  rw [padicValRat_def, hk] at hval
  have h2 : padicValNat 3 (2 ^ k) = 0 :=
    padicValNat.eq_zero_of_not_dvd fun h3 => by
      have := (Nat.prime_three.dvd_of_dvd_pow h3); omega
  rw [h2] at hval
  have : (0 : ℤ) ≤ padicValInt 3 q.num := Int.natCast_nonneg _
  omega

/--
"All denominators are powers of two (A000079)." - _Robert G. Wilson v_, Aug 02 2015

This is false: for $n = 1807$ the denominator of $1/\det(M)$ is divisible by $3$.
See T. Adamczewski, OEIS Open: How many conjectures can language models turn into theorems?,
[arXiv:2608.11941](https://arxiv.org/abs/2608.11941). The Lean disproof there uses the closed
form $1/\det(M) = \prod_{k=1}^n k^2/\varphi(k)$ from the OEIS entry:
https://github.com/epoch-research/LeanOpenProblems-results/blob/fd09021e79869476ef83cda231312f1a2a89c8d7/runs/oeis-full-50usd-ant-j0j0g4uzligm1k41/oeis_60841_conjecture_0/Submission/Spec.lean#L272
-/
@[category research solved, AMS 11 15]
theorem conjecture2 :
    ¬ ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, ((lcmMatrix n).det)⁻¹.den = 2 ^ k := by
  exact a608_main

end OeisA60841
