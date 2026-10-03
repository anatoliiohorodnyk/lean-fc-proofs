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
# Schur's theorem on Galois groups of truncated exponential polynomials

*Reference:* (https://math.stackexchange.com/questions/2814220)

*Reference* (https://mathoverflow.net/questions/477077)
-/

@[expose] public section

/-
Note: This was asked by Nick Katz. Quasi-autoformalized using Claude 4.0 Sonnet.
-/

namespace SchurTruncatedExponential

open Polynomial

open scoped Nat

/--
The truncated exponential polynomial `truncatedExp n` is
given by `∑_{j=0}^{n} x^j / j!` over `ℚ`, which is the
`n`-th partial sum of the Taylor series for the exponential function `e^x`.
-/
noncomputable def truncatedExp (n : ℕ) : ℚ[X] :=
  ∑ j ∈ Finset.range (n + 1), (1 / j ! : ℚ) • X ^ j

open Polynomial Finset in
/-- Splitting `j ≠ i` into `j > i` and `j < i`, and swapping the order in the second part. -/
lemma sch_prod_pairs {M : Type*} [CommMonoid M] {n : ℕ} (F : Fin n → Fin n → M) :
    ∏ i, ∏ j ∈ univ.erase i, F i j =
      (∏ i, ∏ j ∈ Ioi i, F i j) * ∏ i, ∏ j ∈ Ioi i, F j i := by
  have h1 : ∀ i : Fin n, ∏ j ∈ univ.erase i, F i j =
      (∏ j ∈ Ioi i, F i j) * ∏ j ∈ Iio i, F i j := by
    intro i
    rw [← prod_union]
    · congr 1; ext j; simp [lt_or_gt_of_ne, ne_comm, or_comm]
    · rw [disjoint_left]; intro a ha hb; simp at ha hb; omega
  rw [prod_congr rfl (fun i _ => h1 i), prod_mul_distrib]
  congr 1
  apply prod_comm'
  intro x y
  simp

open Polynomial Finset in
/-- `∏_{i ≠ j} (vᵢ - vⱼ) = (-1)^{#pairs} ∏_{i<j} (vⱼ - vᵢ)²`. -/
lemma sch_prod_ne_eq {R : Type*} [CommRing R] {n : ℕ} (v : Fin n → R) :
    ∏ i, ∏ j ∈ univ.erase i, (v i - v j) =
      (-1) ^ (∑ i : Fin n, (Ioi i).card) * (∏ i, ∏ j ∈ Ioi i, (v j - v i)) ^ 2 := by
  rw [sch_prod_pairs, sq, ← mul_assoc]
  congr 1
  rw [← prod_pow_eq_pow_sum, ← prod_mul_distrib]
  apply prod_congr rfl; intro i _
  rw [← prod_neg]
  apply prod_congr rfl; intro j _
  ring

open Polynomial Finset in
/-- `g_n = n! · f_n = ∑_{j ≤ n} (n!/j!) X^j`. -/
noncomputable def schG (R : Type*) [CommRing R] (n : ℕ) : R[X] :=
  ∑ j ∈ range (n + 1), C ((n.factorial / j.factorial : ℕ) : R) * X ^ j

open Polynomial Finset in
lemma sch_fact_div (n k : ℕ) (hk : k < n) :
    n.factorial / (k + 1).factorial * (k + 1) = n.factorial / k.factorial := by
  obtain ⟨m, hm⟩ := Nat.factorial_dvd_factorial (show k + 1 ≤ n by omega)
  have h1 : n.factorial / (k + 1).factorial = m := by
    rw [hm, Nat.mul_div_cancel_left _ (Nat.factorial_pos _)]
  have h2 : n.factorial / k.factorial = (k + 1) * m := by
    rw [hm, Nat.factorial_succ, mul_assoc, mul_comm (k + 1), mul_assoc,
      Nat.mul_div_cancel_left _ (Nat.factorial_pos _)]
    ring
  rw [h1, h2, mul_comm]

open Polynomial Finset in
lemma sch_derivative_G (R : Type*) [CommRing R] (n : ℕ) :
    derivative (schG R n) = schG R n - X ^ n := by
  unfold schG
  rw [derivative_sum, sum_range_succ', sum_range_succ (n := n)]
  simp only [derivative_C_mul_X_pow, Nat.cast_zero, mul_zero, C_0, zero_mul, add_zero,
    Nat.div_self (Nat.factorial_pos n), Nat.cast_one, C_1, one_mul, add_sub_cancel_right]
  apply sum_congr rfl
  intro k hk
  rw [mem_range] at hk
  simp only [Nat.add_sub_cancel]
  congr 2
  rw [← sch_fact_div n k hk]
  push_cast
  ring

open Polynomial Finset in
lemma sch_eval_zero_G (R : Type*) [CommRing R] (n : ℕ) : eval 0 (schG R n) = n.factorial := by
  unfold schG
  rw [eval_finsetSum, sum_range_succ']
  simp

open Polynomial Finset in
/-- Derivative of `∏ (X - vᵢ)` at a root. -/
lemma sch_eval_derivative_prod {L : Type*} [Field L] {n : ℕ} (v : Fin n → L) (i : Fin n) :
    eval (v i) (derivative (∏ j, (X - C (v j)))) = ∏ j ∈ univ.erase i, (v i - v j) := by
  classical
  rw [derivative_prod_finset, eval_finsetSum, sum_eq_single i]
  · simp [eval_prod]
  · intro k _ hk
    rw [eval_mul, eval_prod]
    apply mul_eq_zero_of_left
    apply prod_eq_zero (i := i) (mem_erase.mpr ⟨fun h => hk h.symm, mem_univ _⟩)
    simp
  · simp

open Polynomial Finset in
/-- M6a: the square of the Vandermonde product of the roots of `g_n`. -/
lemma sch_delta_sq {L : Type*} [Field L] {n : ℕ} (v : Fin n → L)
    (hv : schG L n = ∏ i, (X - C (v i))) :
    (∏ i, ∏ j ∈ Ioi i, (v j - v i)) ^ 2 =
      (-1) ^ (∑ i : Fin n, (Ioi i).card) * ((n.factorial : L)) ^ n := by
  have hne : ∏ i, ∏ j ∈ univ.erase i, (v i - v j) = ∏ i : Fin n, (-(v i ^ n)) := by
    apply prod_congr rfl; intro i _
    rw [← sch_eval_derivative_prod, ← hv, sch_derivative_G, eval_sub, hv]
    simp [eval_prod]
    exact prod_eq_zero (mem_univ i) (sub_self _)
  have hprod : ∏ i, v i = (-1) ^ n * (n.factorial : L) := by
    have h0 := sch_eval_zero_G L n
    rw [hv, eval_prod] at h0
    simp only [eval_sub, eval_X, eval_C, zero_sub] at h0
    rw [prod_neg, card_univ, Fintype.card_fin] at h0
    rw [← h0, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
    simp
  have hne' : ∏ i, ∏ j ∈ univ.erase i, (v i - v j) = (n.factorial : L) ^ n := by
    rw [hne, prod_neg, card_univ, Fintype.card_fin, prod_pow, hprod, mul_pow, ← mul_assoc,
      ← pow_mul, ← pow_add]
    have : Even (n + n * n) := by
      rcases Nat.even_or_odd n with h | h
      · exact h.add (h.mul_right n)
      · exact h.add_odd (h.mul h)
    rw [this.neg_one_pow, one_mul]
  have key := sch_prod_ne_eq v
  rw [hne'] at key
  rw [key, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  simp

open Polynomial Finset in
lemma sch_P_eq (n : ℕ) : ∑ i : Fin n, (Ioi i).card = ∑ k ∈ range n, k := by
  simp only [Fin.card_Ioi]
  rw [Fin.sum_univ_eq_sum_range (fun i => n - 1 - i) n]
  rw [← sum_range_reflect]
  apply sum_congr rfl
  intro k hk
  rw [mem_range] at hk
  omega

open Polynomial Finset in
lemma sch_S_mod (n : ℕ) :
    (∑ k ∈ range n, k) % 2 = if n % 4 = 0 ∨ n % 4 = 1 then 0 else 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    split_ifs at ih with h1 <;> split_ifs with h2 <;> omega

open Polynomial Finset in
/-- `n!` is not a square for `n ≥ 2`. -/
lemma sch_factorial_not_square (n : ℕ) (hn : 2 ≤ n) : ¬ IsSquare n.factorial := by
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (n / 2) (by omega)
  haveI := Fact.mk hp
  have hp2 := hp.two_le
  have hv : padicValNat p n.factorial = 1 := by
    rw [padicValNat_factorial (b := 2)]
    · simp only [Nat.Ico_succ_singleton, sum_singleton, pow_one]
      exact Nat.div_eq_of_lt_le (by omega) (by omega)
    · rw [Nat.log_lt_iff_lt_pow hp.one_lt (by omega)]
      have : n < 2 * p := by omega
      nlinarith
  rintro ⟨r, hr⟩
  have hr0 : r ≠ 0 := by rintro rfl; simp at hr; exact Nat.factorial_ne_zero n hr
  rw [hr, padicValNat.mul hr0 hr0] at hv
  omega

open Polynomial Finset in
/-- M6b: `(-1)^{n(n-1)/2} (n!)^n` is a rational square iff `4 ∣ n` (for `n ≥ 2`). -/
lemma sch_square_iff (n : ℕ) (hn : 2 ≤ n) :
    IsSquare ((-1 : ℚ) ^ (∑ k ∈ range n, k) * (n.factorial : ℚ) ^ n) ↔ n % 4 = 0 := by
  have hS := sch_S_mod n
  have hf0 : (0 : ℚ) < (n.factorial : ℚ) ^ n := by positivity
  constructor
  · intro hsq
    by_contra h4
    rcases Nat.even_or_odd (∑ k ∈ range n, k) with he | ho
    · -- then `n % 4 = 1`, `n` odd
      have h1 : n % 4 = 1 := by
        rw [Nat.even_iff] at he; split_ifs at hS <;> omega
      rw [he.neg_one_pow, one_mul] at hsq
      obtain ⟨m, hm⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
      obtain ⟨q, hq⟩ := hsq
      have hF : (n.factorial : ℚ) ≠ 0 := by positivity
      have : IsSquare (n.factorial : ℚ) := by
        refine ⟨q / (n.factorial : ℚ) ^ m, ?_⟩
        field_simp
        calc (n.factorial : ℚ) * ((n.factorial : ℚ) ^ m) ^ 2
            = (n.factorial : ℚ) ^ (2 * m + 1) := by ring
          _ = (n.factorial : ℚ) ^ n := by rw [← hm]
          _ = q * q := hq
          _ = q ^ 2 := by ring
      exact sch_factorial_not_square n hn (Rat.isSquare_natCast_iff.mp this)
    · rw [ho.neg_one_pow, neg_one_mul] at hsq
      obtain ⟨q, hq⟩ := hsq
      nlinarith [mul_self_nonneg q]
  · intro h4
    have he : Even (∑ k ∈ range n, k) := by
      rw [Nat.even_iff]; split_ifs at hS <;> omega
    rw [he.neg_one_pow, one_mul]
    obtain ⟨m, hm⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
    exact ⟨(n.factorial : ℚ) ^ m, by rw [hm, pow_mul, sq]; ring_nf⟩

open Polynomial Finset in
/-- M6c: an automorphism permuting the roots multiplies the Vandermonde determinant by the sign. -/
lemma sch_sigma_delta {F L : Type*} [Field F] [Field L] [Algebra F L] {n : ℕ} (v : Fin n → L)
    (σ : L ≃ₐ[F] L) (π : Equiv.Perm (Fin n)) (hπ : ∀ i, σ (v i) = v (π i)) :
    σ (Matrix.vandermonde v).det = (Equiv.Perm.sign π : ℤ) * (Matrix.vandermonde v).det := by
  have h1 : σ (Matrix.vandermonde v).det = (Matrix.vandermonde (v ∘ π)).det := by
    rw [show σ (Matrix.vandermonde v).det = (σ : L →+* L) (Matrix.vandermonde v).det from rfl,
      RingHom.map_det]
    congr 1
    ext i j
    simp [Matrix.vandermonde_apply, hπ]
  rw [h1, ← Matrix.det_permute]
  congr 1


open Polynomial Finset in
/-- M1a: in an ultrametric normed field, if a finite sum vanishes and some term is nonzero, the
maximal norm is attained at two different indices. -/
lemma sch_ultra_two_max {K : Type*} [NormedField K] [IsUltrametricDist K] {ι : Type*}
    [DecidableEq ι] (s : Finset ι) (x : ι → K) (hsum : ∑ j ∈ s, x j = 0)
    (hne : ∃ j ∈ s, x j ≠ 0) :
    ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ (∀ m ∈ s, ‖x m‖ ≤ ‖x i‖) ∧ ‖x j‖ = ‖x i‖ := by
  obtain ⟨j0, hj0, hx0⟩ := hne
  obtain ⟨i, hi, himax⟩ := s.exists_max_image (fun j => ‖x j‖) ⟨j0, hj0⟩
  have hipos : 0 < ‖x i‖ := lt_of_lt_of_le (norm_pos_iff.mpr hx0) (himax j0 hj0)
  by_contra hcon
  push Not at hcon
  have hlt : ∀ m ∈ s.erase i, ‖x m‖ < ‖x i‖ := by
    intro m hm
    obtain ⟨hmi, hms⟩ := Finset.mem_erase.mp hm
    exact lt_of_le_of_ne (himax m hms) (hcon i hi m hms (Ne.symm hmi) himax)
  have hrest : ‖∑ m ∈ s.erase i, x m‖ < ‖x i‖ := by
    rcases (s.erase i).eq_empty_or_nonempty with he | he
    · rw [he, Finset.sum_empty, norm_zero]; exact hipos
    · haveI : Nonempty ι := ⟨i⟩
      obtain ⟨m, hm, hmle⟩ := IsUltrametricDist.exists_norm_finsetSum_le (s.erase i) x
      exact lt_of_le_of_lt hmle (hlt m (hm he))
  have hsplit : ∑ j ∈ s, x j = x i + ∑ m ∈ s.erase i, x m := (Finset.add_sum_erase s x hi).symm
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt hrest)
  rw [← hsplit, hsum, norm_zero, max_eq_left hrest.le] at this
  linarith

open Polynomial Finset in
/-- Base-`p` digit sum. -/
abbrev schS (p j : ℕ) : ℕ := (p.digits j).sum

open Polynomial Finset in
lemma sch_S_step {p : ℕ} (hp : 1 < p) (y : ℕ) : schS p y = y % p + schS p (y / p) := by
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · simp [schS]
  · unfold schS; rw [Nat.digits_def' hp hy, List.sum_cons]

open Polynomial Finset in
lemma sch_S_split {p : ℕ} (hp : 1 < p) (r : ℕ) :
    ∀ H L, L < p ^ r → schS p (H * p ^ r + L) = schS p H + schS p L := by
  induction r with
  | zero => intro H L hL; simp at hL; subst hL; simp [schS]
  | succ r ih =>
    intro H L hL
    rw [sch_S_step hp (H * p ^ (r + 1) + L), sch_S_step hp L]
    have hp0 : 0 < p := by omega
    have h1 : (H * p ^ (r + 1) + L) % p = L % p := by
      rw [pow_succ, ← mul_assoc, Nat.add_comm, Nat.add_mul_mod_self_right]
    have h2 : (H * p ^ (r + 1) + L) / p = H * p ^ r + L / p := by
      rw [pow_succ, ← mul_assoc, Nat.add_comm, Nat.add_mul_div_right _ _ hp0, Nat.add_comm]
    have h3 : L / p < p ^ r := by
      rw [Nat.div_lt_iff_lt_mul hp0]; rwa [← pow_succ]
    rw [h1, h2, ih H (L / p) h3]
    ring

open Polynomial Finset in
lemma sch_S_lt {p : ℕ} (hp : 1 < p) {D : ℕ} (hD : D < p) : schS p D = D := by
  rw [sch_S_step hp, Nat.mod_eq_of_lt hD, Nat.div_eq_of_lt hD]; simp [schS]

open Polynomial Finset in
lemma sch_S_pos {p : ℕ} (hp : 1 < p) {y : ℕ} (hy : 0 < y) : 1 ≤ schS p y := by
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    rw [sch_S_step hp]
    rcases Nat.eq_zero_or_pos (y % p) with h | h
    · have hy' : 0 < y / p := by
        rcases Nat.eq_zero_or_pos (y / p) with h' | h'
        · have := Nat.div_add_mod y p; rw [h', h] at this; omega
        · exact h'
      have := ih (y / p) (Nat.div_lt_self hy hp) hy'
      omega
    · omega

open Polynomial Finset in
/-- `s(x+1) ≤ s(x) + 1`, via Legendre's formula. -/
lemma sch_S_succ_le (p : ℕ) [hp : Fact p.Prime] (x : ℕ) : schS p (x + 1) ≤ schS p x + 1 := by
  have h1 := sub_one_mul_padicValNat_factorial (p := p) x
  have h2 := sub_one_mul_padicValNat_factorial (p := p) (x + 1)
  have hmono : padicValNat p x.factorial ≤ padicValNat p (x + 1).factorial := by
    apply padicValNat_dvd_iff_le (Nat.factorial_ne_zero _) |>.mp
    exact (pow_padicValNat_dvd).trans (Nat.factorial_dvd_factorial (by omega))
  have hs1 := Nat.digit_sum_le p x
  have hs2 := Nat.digit_sum_le p (x + 1)
  have : (p - 1) * padicValNat p x.factorial ≤ (p - 1) * padicValNat p (x + 1).factorial :=
    Nat.mul_le_mul_left _ hmono
  unfold schS
  omega

open Polynomial Finset in
lemma sch_S_le_add (p : ℕ) [Fact p.Prime] (H d : ℕ) : schS p (H + d) ≤ schS p H + d := by
  induction d with
  | zero => simp
  | succ d ih => have := sch_S_succ_le p (H + d); rw [← add_assoc]; omega

open Polynomial Finset in
/-- `F_t(j) = s(j) - t j`. -/
noncomputable abbrev schF (p : ℕ) (t : ℝ) (j : ℕ) : ℝ := (schS p j : ℝ) - t * j

open Polynomial Finset in
/-- Comparison with `N p^{k+1}` (`N = ⌊n / p^{k+1}⌋`) when `p^{-(k+1)} < t ≤ p^{-k}`. -/
lemma sch_F_compare (p : ℕ) [hp : Fact p.Prime] (t : ℝ) (k n j : ℕ)
    (hlo : ((p : ℝ) ^ (k + 1))⁻¹ < t) (hhi : t ≤ ((p : ℝ) ^ k)⁻¹) (hj : j ≤ n) :
    schF p t (n / p ^ (k + 1) * p ^ (k + 1)) ≤ schF p t j ∧
      (schF p t j = schF p t (n / p ^ (k + 1) * p ^ (k + 1)) →
        j / p ^ (k + 1) = n / p ^ (k + 1) ∧ j % p ^ k = 0 ∧
          ((j / p ^ k) % p = 0 ∨ t = ((p : ℝ) ^ k)⁻¹)) := by
  have hp1 := hp.out.one_lt
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hpk : (0 : ℝ) < (p : ℝ) ^ k := pow_pos hpR k
  set N := n / p ^ (k + 1)
  set H := j / p ^ (k + 1)
  set D := (j % p ^ (k + 1)) / p ^ k
  set L := (j % p ^ (k + 1)) % p ^ k
  have hpk1 : p ^ (k + 1) = p ^ k * p := pow_succ p k
  have hjdec : j = H * p ^ (k + 1) + (D * p ^ k + L) := by
    have e1 := Nat.div_add_mod j (p ^ (k + 1))
    have e2 := Nat.div_add_mod (j % p ^ (k + 1)) (p ^ k)
    simp only [H, D, L]; nlinarith [e1, e2]
  have hLlt : L < p ^ k := Nat.mod_lt _ (by positivity)
  have hDlt : D < p := by
    simp only [D]; rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_succ']
    exact Nat.mod_lt _ (by positivity)
  have hDL : D * p ^ k + L < p ^ (k + 1) := by
    rw [hpk1]; nlinarith
  have hsj : schS p j = schS p H + D + schS p L := by
    rw [hjdec, sch_S_split hp1 (k + 1) H _ hDL, sch_S_split hp1 k D L hLlt, sch_S_lt hp1 hDlt]
    ring
  have hsN : schS p (N * p ^ (k + 1)) = schS p N := by
    have := sch_S_split hp1 (k + 1) N 0 (by positivity); simpa [schS] using this
  have hHN : H ≤ N := Nat.div_le_div_right hj
  have hsub : schS p N ≤ schS p H + (N - H) := by
    have := sch_S_le_add p H (N - H); rwa [Nat.add_sub_cancel' hHN] at this
  -- real-valued pieces
  set c : ℝ := t * (p : ℝ) ^ (k + 1)
  have hc1 : 1 < c := by
    have := mul_lt_mul_of_pos_right hlo (pow_pos hpR (k + 1))
    rwa [inv_mul_cancel₀ (pow_pos hpR (k + 1)).ne'] at this
  have htpk : t * (p : ℝ) ^ k ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hhi hpk.le
    rwa [inv_mul_cancel₀ hpk.ne'] at this
  have hLterm : 0 ≤ (schS p L : ℝ) - t * L ∧ (L ≠ 0 → 0 < (schS p L : ℝ) - t * L) := by
    have ht0 : 0 < t := lt_trans (by positivity) hlo
    have hL1 : t * (L : ℝ) < 1 ∨ L = 0 := by
      rcases Nat.eq_zero_or_pos L with h | h
      · exact Or.inr h
      · left
        have hLR : (L : ℝ) < (p : ℝ) ^ k := by exact_mod_cast hLlt
        calc t * (L : ℝ) ≤ ((p : ℝ) ^ k)⁻¹ * L := by gcongr
          _ < ((p : ℝ) ^ k)⁻¹ * (p : ℝ) ^ k := by gcongr
          _ = 1 := inv_mul_cancel₀ hpk.ne'
    constructor
    · rcases hL1 with h | h
      · rcases Nat.eq_zero_or_pos L with h0 | h0
        · simp [h0, schS]
        · have := sch_S_pos hp1 h0
          have : (1 : ℝ) ≤ schS p L := by exact_mod_cast this
          linarith
      · simp [h, schS]
    · intro hL0
      rcases hL1 with h | h
      · have := sch_S_pos hp1 (Nat.pos_of_ne_zero hL0)
        have : (1 : ℝ) ≤ schS p L := by exact_mod_cast this
        linarith
      · exact absurd h hL0
  have hDterm : 0 ≤ (D : ℝ) * (1 - t * (p : ℝ) ^ k) := by
    apply mul_nonneg (by positivity); linarith
  have hHterm : (schS p N : ℝ) - c * N ≤ (schS p H : ℝ) - c * H ∧
      (H < N → (schS p N : ℝ) - c * N < (schS p H : ℝ) - c * H) := by
    have hsubR : (schS p N : ℝ) ≤ schS p H + ((N : ℝ) - H) := by
      have h := (Nat.cast_le (α := ℝ)).mpr hsub
      rw [Nat.cast_add, Nat.cast_sub hHN] at h
      exact h
    have hHNR : (H : ℝ) ≤ N := by exact_mod_cast hHN
    constructor
    · nlinarith
    · intro hlt
      have : (H : ℝ) < N := by exact_mod_cast hlt
      nlinarith
  have hFj : schF p t j = ((schS p H : ℝ) - c * H) + (D : ℝ) * (1 - t * (p : ℝ) ^ k) +
      ((schS p L : ℝ) - t * L) := by
    simp only [schF, hsj, c]
    rw [hjdec]; push_cast; ring
  have hF0 : schF p t (N * p ^ (k + 1)) = (schS p N : ℝ) - c * N := by
    simp only [schF, hsN, c]; push_cast; ring
  refine ⟨by rw [hFj, hF0]; linarith [hLterm.1, hHterm.1], fun heq => ?_⟩
  rw [hFj, hF0] at heq
  have hHeq : H = N := by
    by_contra hne
    have := hHterm.2 (lt_of_le_of_ne hHN hne)
    linarith [hLterm.1]
  have hL0 : L = 0 := by
    by_contra hne
    have := hLterm.2 hne
    linarith [hHterm.1]
  have hD0 : (D : ℝ) * (1 - t * (p : ℝ) ^ k) = 0 := by linarith [hLterm.1, hHterm.1]
  refine ⟨hHeq, ?_, ?_⟩
  · have : j % p ^ k = L := by
      rw [hjdec, Nat.add_mod, Nat.mul_mod, show p ^ (k + 1) % p ^ k = 0 by
        rw [pow_succ]; exact Nat.mul_mod_right _ _]
      simp [Nat.add_mod, Nat.mod_eq_of_lt hLlt]
    rw [this, hL0]
  · rcases mul_eq_zero.mp hD0 with h | h
    · left
      have hD : D = 0 := by exact_mod_cast h
      have : (j / p ^ k) % p = D := by
        rw [hjdec, hpk1, hL0, add_zero]
        rw [show H * (p ^ k * p) + D * p ^ k = (H * p + D) * p ^ k by ring,
          Nat.mul_div_cancel _ (by positivity), Nat.add_mod, Nat.mul_mod_left, zero_add,
          Nat.mod_mod, Nat.mod_eq_of_lt hDlt]
      rw [this, hD]
    · right
      have : t * (p : ℝ) ^ k = 1 := by linarith
      field_simp
      linarith

open Polynomial Finset in
/-- M2: if `F_t` has two different minimizers on `[0, n]`, then `t = p^{-k}` for some `k` such that
the `k`-th base-`p` digit of `n` is nonzero. -/
lemma sch_two_min (p : ℕ) [hp : Fact p.Prime] (t : ℝ) (n i j : ℕ) (hij : i ≠ j)
    (hi : i ≤ n) (hj : j ≤ n) (hmin_i : ∀ m ≤ n, schF p t i ≤ schF p t m)
    (hmin_j : ∀ m ≤ n, schF p t j ≤ schF p t m) :
    ∃ k : ℕ, t = ((p : ℝ) ^ k)⁻¹ ∧ (n / p ^ k) % p ≠ 0 := by
  have hp1 := hp.out.one_lt
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp1
  -- `F` takes the value `0` at `0` and is positive elsewhere when `t ≤ 0`
  rcases le_or_gt t 0 with ht0 | ht0
  · exfalso
    have hpos : ∀ m, 0 < m → 0 < schF p t m := by
      intro m hm
      have h1 : (1 : ℝ) ≤ schS p m := by exact_mod_cast sch_S_pos hp1 hm
      have : t * (m : ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ht0 (by positivity)
      simp only [schF]; linarith
    have hF0 : schF p t 0 = 0 := by simp [schF, schS]
    have hi0 : i = 0 := by
      by_contra h; have := hpos i (Nat.pos_of_ne_zero h); have := hmin_i 0 (Nat.zero_le _); linarith
    have hj0 : j = 0 := by
      by_contra h; have := hpos j (Nat.pos_of_ne_zero h); have := hmin_j 0 (Nat.zero_le _); linarith
    exact hij (hi0.trans hj0.symm)
  rcases lt_or_ge 1 t with ht1 | ht1
  · -- `F` is strictly decreasing towards `n`
    exfalso
    have hlt : ∀ m, m < n → schF p t n < schF p t m := by
      intro m hm
      have hs := sch_S_le_add p m (n - m)
      rw [Nat.add_sub_cancel' hm.le] at hs
      have hsR : (schS p n : ℝ) ≤ schS p m + ((n : ℝ) - m) := by
        have h := (Nat.cast_le (α := ℝ)).mpr hs
        rw [Nat.cast_add, Nat.cast_sub hm.le] at h; exact h
      have hmn : (m : ℝ) < n := by exact_mod_cast hm
      simp only [schF]; nlinarith
    have hin : i = n := by
      by_contra h; have := hlt i (lt_of_le_of_ne hi h); have := hmin_i n le_rfl; linarith
    have hjn : j = n := by
      by_contra h; have := hlt j (lt_of_le_of_ne hj h); have := hmin_j n le_rfl; linarith
    exact hij (hin.trans hjn.symm)
  -- `0 < t ≤ 1`: locate `t` between consecutive powers of `p⁻¹`
  have hex : ∃ k : ℕ, ((p : ℝ) ^ (k + 1))⁻¹ < t := by
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one ht0 (inv_lt_one_of_one_lt₀ hpR)
    exact ⟨k, by rw [← inv_pow]; exact lt_of_le_of_lt (pow_le_pow_of_le_one (by positivity)
      (inv_le_one_of_one_le₀ hpR.le) (Nat.le_succ k)) hk⟩
  classical
  set k := Nat.find hex
  have hlo : ((p : ℝ) ^ (k + 1))⁻¹ < t := Nat.find_spec hex
  have hhi : t ≤ ((p : ℝ) ^ k)⁻¹ := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · rw [hk]; simpa using ht1
    · have := Nat.find_min hex (show k - 1 < k by omega)
      push Not at this
      rwa [show k - 1 + 1 = k by omega] at this
  set N := n / p ^ (k + 1)
  obtain ⟨hci, hci'⟩ := sch_F_compare p t k n i hlo hhi hi
  obtain ⟨hcj, hcj'⟩ := sch_F_compare p t k n j hlo hhi hj
  have hN : N * p ^ (k + 1) ≤ n := Nat.div_mul_le_self _ _
  obtain ⟨hHi, hLi, hDi⟩ := hci' (le_antisymm (hmin_i _ hN) hci)
  obtain ⟨hHj, hLj, hDj⟩ := hcj' (le_antisymm (hmin_j _ hN) hcj)
  -- decompose `i`, `j` and `n` in base `p` around position `k`
  have hpk1 : p ^ (k + 1) = p ^ k * p := pow_succ p k
  have hdec : ∀ m, m = (m / p ^ (k + 1)) * p ^ (k + 1) + ((m / p ^ k) % p) * p ^ k + m % p ^ k := by
    intro m
    have e1 := Nat.div_add_mod m (p ^ k)
    have e2 := Nat.div_add_mod (m / p ^ k) p
    have e3 : m / p ^ (k + 1) = m / p ^ k / p := by rw [pow_succ, Nat.div_div_eq_div_mul]
    rw [e3, hpk1]
    calc m = p ^ k * (m / p ^ k) + m % p ^ k := e1.symm
      _ = p ^ k * (p * (m / p ^ k / p) + (m / p ^ k) % p) + m % p ^ k := by rw [e2]
      _ = _ := by ring
  have hdi := hdec i
  have hdj := hdec j
  have hdn := hdec n
  rw [hHi, hLi] at hdi
  rw [hHj, hLj] at hdj
  have hDi_le : (i / p ^ k) % p ≤ (n / p ^ k) % p := by
    have hpos : 0 < p ^ k := by positivity
    have hr := Nat.mod_lt n hpos
    by_contra h; push Not at h
    have h2 : ((n / p ^ k) % p + 1) * p ^ k ≤ ((i / p ^ k) % p) * p ^ k := Nat.mul_le_mul_right _ h
    rw [add_mul, one_mul] at h2
    have := hdi
    omega
  have hDj_le : (j / p ^ k) % p ≤ (n / p ^ k) % p := by
    have hpos : 0 < p ^ k := by positivity
    have hr := Nat.mod_lt n hpos
    by_contra h; push Not at h
    have h2 : ((n / p ^ k) % p + 1) * p ^ k ≤ ((j / p ^ k) % p) * p ^ k := Nat.mul_le_mul_right _ h
    rw [add_mul, one_mul] at h2
    have := hdj
    omega
  -- the digits at position `k` differ, so `t = p^{-k}` and the digit of `n` is nonzero
  have hdiff : (i / p ^ k) % p ≠ (j / p ^ k) % p := by
    intro h; apply hij; rw [hdi, hdj, h]
  refine ⟨k, ?_, ?_⟩
  · rcases hDi with h | h
    · rcases hDj with h' | h'
      · exact absurd (h.trans h'.symm) hdiff
      · exact h'
    · exact h
  · omega

open Polynomial Finset in
lemma sch_norm_natCast (p : ℕ) [hp : Fact p.Prime] (c : ℕ) (hc : c ≠ 0) :
    ‖(c : PadicAlgCl p)‖ = (p : ℝ) ^ (-(padicValNat p c : ℝ)) := by
  have h1 : (c : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) (c : ℚ_[p]) := by simp
  rw [h1, PadicAlgCl.norm_extends, Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hc),
    Padic.valuation_natCast, ← Real.rpow_intCast]
  simp

open Polynomial Finset in
/-- M1: the norm of a root of `g_n = ∑ (n!/j!) X^j` in `ℂ_p`-algebraic closure is
`p^{-(1 - p^{-k})/(p-1)}` for some `k` such that the `k`-th base-`p` digit of `n` is nonzero. -/
lemma sch_root_norm (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (α : PadicAlgCl p)
    (hα : ∑ j ∈ Finset.range (n + 1),
      ((n.factorial / j.factorial : ℕ) : PadicAlgCl p) * α ^ j = 0) :
    ∃ k : ℕ, (n / p ^ k) % p ≠ 0 ∧
      ‖α‖ = (p : ℝ) ^ (-((1 - ((p : ℝ) ^ k)⁻¹) / ((p : ℝ) - 1))) := by
  classical
  have hp1 := hp.out.one_lt
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp1
  have hpR0 : (0 : ℝ) < p := by linarith
  have hcoef : ∀ j ∈ Finset.range (n + 1), n.factorial / j.factorial ≠ 0 := by
    intro j hj
    rw [Finset.mem_range] at hj
    exact (Nat.div_pos (Nat.factorial_le (by omega)) (Nat.factorial_pos _)).ne'
  -- `α ≠ 0`
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [Finset.sum_range_succ'] at hα
    simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
      zero_pow, mul_zero, Finset.sum_const_zero, pow_zero, mul_one, zero_add,
      Nat.factorial_zero, Nat.div_one, Nat.cast_eq_zero] at hα
    exact Nat.factorial_ne_zero n hα
  set ρ := ‖α‖
  have hρ : 0 < ρ := norm_pos_iff.mpr hα0
  set μ := -Real.logb p ρ
  have hρμ : ‖α‖ = (p : ℝ) ^ (-μ) := by
    simp only [μ, neg_neg]; rw [Real.rpow_logb hpR0 hpR.ne' hρ]
  set v : ℕ → ℕ := fun j => padicValNat p (n.factorial / j.factorial)
  set E : ℕ → ℝ := fun j => (v j : ℝ) + j * μ
  have hterm : ∀ j ∈ Finset.range (n + 1),
      ‖((n.factorial / j.factorial : ℕ) : PadicAlgCl p) * α ^ j‖ = (p : ℝ) ^ (-E j) := by
    intro j hj
    rw [norm_mul, norm_pow, sch_norm_natCast p _ (hcoef j hj), hρμ, ← Real.rpow_natCast,
      ← Real.rpow_mul hpR0.le, ← Real.rpow_add hpR0]
    congr 1; simp only [E]; ring
  obtain ⟨i, hi, j, hj, hij, hmax, heq⟩ := sch_ultra_two_max (Finset.range (n + 1))
    (fun j => ((n.factorial / j.factorial : ℕ) : PadicAlgCl p) * α ^ j) hα
    ⟨0, by simp, by simp [Nat.factorial_ne_zero]⟩
  have hEmin : ∀ m ∈ Finset.range (n + 1), E i ≤ E m := by
    intro m hm
    have := hmax m hm
    rw [hterm m hm, hterm i hi, Real.rpow_le_rpow_left_iff hpR] at this
    linarith
  have hEeq : E j = E i := by
    rw [hterm j hj, hterm i hi] at heq
    have h := congrArg (Real.logb p) heq
    rw [Real.logb_rpow hpR0 hpR.ne', Real.logb_rpow hpR0 hpR.ne'] at h
    linarith
  -- translate to `F_t` with `t = 1 - (p - 1) μ`
  set t : ℝ := 1 - ((p : ℝ) - 1) * μ
  set C : ℝ := ((p : ℝ) - 1) * padicValNat p n.factorial
  have hEF : ∀ m ≤ n, ((p : ℝ) - 1) * E m = C + schF p t m := by
    intro m hm
    have hdvd : m.factorial ∣ n.factorial := Nat.factorial_dvd_factorial hm
    have hv : v m = padicValNat p n.factorial - padicValNat p m.factorial :=
      padicValNat.div_of_dvd hdvd
    have hle : padicValNat p m.factorial ≤ padicValNat p n.factorial :=
      (padicValNat_dvd_iff_le (Nat.factorial_ne_zero _)).mp
        ((pow_padicValNat_dvd).trans hdvd)
    have hleg := sub_one_mul_padicValNat_factorial (p := p) m
    have hsm := Nat.digit_sum_le p m
    have hlegR : ((p : ℝ) - 1) * padicValNat p m.factorial = m - schS p m := by
      have h := congrArg (Nat.cast (R := ℝ)) hleg
      rw [Nat.cast_mul, Nat.cast_sub hp1.le, Nat.cast_sub hsm] at h
      simpa [schS] using h
    simp only [E, schF, C, t, hv]
    rw [Nat.cast_sub hle]
    linear_combination -hlegR
  have hmin_i : ∀ m ≤ n, schF p t i ≤ schF p t m := by
    intro m hm
    have h1 := hEF i (by simpa [Nat.lt_succ_iff] using hi)
    have h2 := hEF m hm
    have h3 := hEmin m (by simp; omega)
    have hp0 : (0 : ℝ) < p - 1 := by linarith
    nlinarith
  have hmin_j : ∀ m ≤ n, schF p t j ≤ schF p t m := by
    intro m hm
    have h1 := hEF j (by simpa [Nat.lt_succ_iff] using hj)
    have h2 := hEF m hm
    have h3 := hEmin m (by simp; omega)
    have hp0 : (0 : ℝ) < p - 1 := by linarith
    nlinarith
  obtain ⟨k, hk, hdig⟩ := sch_two_min p t n i j hij
    (by simpa [Nat.lt_succ_iff] using hi) (by simpa [Nat.lt_succ_iff] using hj) hmin_i hmin_j
  refine ⟨k, hdig, ?_⟩
  show ‖α‖ = _
  rw [hρμ]
  congr 1
  have hp0 : ((p : ℝ) - 1) ≠ 0 := by linarith
  simp only [t] at hk
  have hμ : μ = (1 - ((p : ℝ) ^ k)⁻¹) / ((p : ℝ) - 1) := by
    rw [eq_div_iff hp0]; linarith
  rw [hμ]

open Polynomial Finset in
/-- All roots (in `PadicAlgCl p`) of the minimal polynomial of `α` have the norm of `α`. -/
lemma sch_norm_conj (p : ℕ) [hp : Fact p.Prime] (α β : PadicAlgCl p)
    (hβ : Polynomial.aeval β (minpoly ℚ_[p] α) = 0) : ‖β‖ = ‖α‖ := by
  have hαi : IsIntegral ℚ_[p] α := Algebra.IsIntegral.isIntegral α
  have hm : minpoly ℚ_[p] β = minpoly ℚ_[p] α :=
    (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hαi) hβ (minpoly.monic hαi)).symm
  rw [NormedAlgebra.norm_eq_spectralNorm ℚ_[p] β, NormedAlgebra.norm_eq_spectralNorm ℚ_[p] α,
    spectralNorm.eq_def, spectralNorm.eq_def, hm]

open Polynomial Finset in
/-- M3a: a root of level `k` has a minimal polynomial over `ℚ_p` of degree divisible by `p ^ k`. -/
lemma sch_level_dvd (p : ℕ) [hp : Fact p.Prime] (α : PadicAlgCl p) (k : ℕ)
    (hα : ‖α‖ = (p : ℝ) ^ (-((1 - ((p : ℝ) ^ k)⁻¹) / ((p : ℝ) - 1)))) :
    p ^ k ∣ (minpoly ℚ_[p] α).natDegree := by
  classical
  have hp1 := hp.out.one_lt
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp1
  have hpR0 : (0 : ℝ) < p := by linarith
  set μ : ℝ := (1 - ((p : ℝ) ^ k)⁻¹) / ((p : ℝ) - 1)
  have hαi : IsIntegral ℚ_[p] α := Algebra.IsIntegral.isIntegral α
  have hα0 : α ≠ 0 := by
    intro h; rw [h, norm_zero] at hα; exact (Real.rpow_pos_of_pos hpR0 _).ne' hα.symm
  set m := minpoly ℚ_[p] α
  set e := m.natDegree
  have hmon : m.Monic := minpoly.monic hαi
  set mL := m.map (algebraMap ℚ_[p] (PadicAlgCl p))
  have hsplit : mL.Splits := IsAlgClosed.splits _
  have hmonL : mL.Monic := hmon.map _
  have hdegL : mL.natDegree = e := hmon.natDegree_map _
  have hcard : mL.roots.card = e := by rw [← hdegL]; exact Polynomial.splits_iff_card_roots.mp hsplit
  have hroots : ∀ β ∈ mL.roots, ‖β‖ = ‖α‖ := by
    intro β hβ
    apply sch_norm_conj
    have := (Polynomial.mem_roots hmonL.ne_zero).mp hβ
    rwa [Polynomial.IsRoot, Polynomial.eval_map_algebraMap] at this
  have hc0 := hsplit.coeff_zero_eq_prod_roots_of_monic hmonL
  rw [hdegL, Polynomial.coeff_map] at hc0
  have hnorm : ‖m.coeff 0‖ = ‖α‖ ^ e := by
    rw [← PadicAlgCl.norm_extends, hc0, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      ← hcard]
    have h1 : ‖mL.roots.prod‖ = (mL.roots.map (fun x => ‖x‖)).prod :=
      map_multiset_prod (normHom (α := PadicAlgCl p)) mL.roots
    rw [h1, Multiset.map_congr rfl hroots, Multiset.map_const', Multiset.prod_replicate]
  -- `‖m.coeff 0‖ = p ^ (-val)` with `val : ℤ`
  have hc0ne : m.coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hαi hα0
  rw [Padic.norm_eq_zpow_neg_valuation hc0ne, hα, ← Real.rpow_natCast, ← Real.rpow_mul hpR0.le,
    ← Real.rpow_intCast] at hnorm
  have hexp := congrArg (Real.logb p) hnorm
  rw [Real.logb_rpow hpR0 hpR.ne', Real.logb_rpow hpR0 hpR.ne'] at hexp
  set val := (m.coeff 0).valuation
  -- `e (p^k - 1) = val (p - 1) p^k`
  have hpk : (0 : ℝ) < (p : ℝ) ^ k := pow_pos hpR0 k
  have hp0 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hreal : (e : ℝ) * ((p : ℝ) ^ k - 1) = (val : ℝ) * ((p : ℝ) - 1) * (p : ℝ) ^ k := by
    have h2 : (val : ℝ) = μ * e := by push_cast at hexp; linarith
    rw [h2]
    simp only [μ]
    field_simp
  have hint : (e : ℤ) * ((p : ℤ) ^ k - 1) = val * ((p : ℤ) - 1) * (p : ℤ) ^ k := by
    exact_mod_cast hreal
  have hdvd : ((p : ℤ) ^ k) ∣ (e : ℤ) * ((p : ℤ) ^ k - 1) := ⟨val * ((p : ℤ) - 1), by rw [hint]; ring⟩
  have hcop : IsCoprime ((p : ℤ) ^ k) ((p : ℤ) ^ k - 1) := ⟨1, -1, by ring⟩
  have := hcop.dvd_of_dvd_mul_right hdvd
  exact_mod_cast this

open Polynomial Finset in
open Polynomial in
/-- If every root of a monic `h ∈ ℚ_p[X]` has a minimal polynomial of degree divisible by `q`,
then `q ∣ deg h`. -/
lemma sch_deg_dvd_of_roots (p : ℕ) [hp : Fact p.Prime] (q : ℕ) :
    ∀ (d : ℕ) (h : ℚ_[p][X]), h.natDegree = d → h.Monic →
      (∀ β : PadicAlgCl p, aeval β h = 0 → q ∣ (minpoly ℚ_[p] β).natDegree) → q ∣ d := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro h hd hmon hroots
    rcases Nat.eq_zero_or_pos d with hd0 | hd0
    · rw [hd0]; exact dvd_zero q
    obtain ⟨β, hβ⟩ := IsAlgClosed.exists_root (h.map (algebraMap ℚ_[p] (PadicAlgCl p)))
      (by rw [degree_map, degree_eq_natDegree hmon.ne_zero, hd]; exact_mod_cast hd0.ne')
    have hβ' : aeval β h = 0 := by rwa [IsRoot, eval_map_algebraMap] at hβ
    have hβi : IsIntegral ℚ_[p] β := Algebra.IsIntegral.isIntegral β
    obtain ⟨h', hh'⟩ := minpoly.dvd ℚ_[p] β hβ'
    have hrmon := minpoly.monic hβi
    have hh'mon : h'.Monic := hrmon.of_mul_monic_left (hh' ▸ hmon)
    have hdeg : d = (minpoly ℚ_[p] β).natDegree + h'.natDegree := by
      rw [← hd, hh', hrmon.natDegree_mul hh'mon]
    have hpos : 0 < (minpoly ℚ_[p] β).natDegree := minpoly.natDegree_pos hβi
    have hq1 := hroots β hβ'
    have hq2 := ih h'.natDegree (by omega) h' rfl hh'mon (fun γ hγ => hroots γ (by
      rw [hh', map_mul, hγ, mul_zero]))
    rw [hdeg]; exact dvd_add hq1 hq2

open Polynomial Finset in
open Polynomial in
lemma sch_G_eq (n : ℕ) : schG ℚ n = X ^ n + ∑ j ∈ Finset.range n,
    C ((n.factorial / j.factorial : ℕ) : ℚ) * X ^ j := by
  unfold schG
  rw [Finset.sum_range_succ, Nat.div_self (Nat.factorial_pos n)]
  simp [add_comm]

open Polynomial Finset in
open Polynomial in
lemma sch_G_monic (n : ℕ) : (schG ℚ n).Monic ∧ (schG ℚ n).natDegree = n := by
  rw [sch_G_eq]
  have hlt : (∑ j ∈ Finset.range n, C ((n.factorial / j.factorial : ℕ) : ℚ) * X ^ j).degree <
      (n : WithBot ℕ) := by
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).mpr ?_
    intro j hj
    rw [Finset.mem_range] at hj
    exact lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) (WithBot.coe_lt_coe.mpr hj)
  have hm := monic_X_pow_add hlt
  refine ⟨hm, ?_⟩
  rw [natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]

open Polynomial Finset in
open Polynomial in
lemma sch_aeval_G {L : Type*} [Field L] [CharZero L] (n : ℕ) (β : L) :
    aeval β (schG ℚ n) = ∑ j ∈ Finset.range (n + 1), ((n.factorial / j.factorial : ℕ) : L) * β ^ j := by
  simp [schG, map_sum]

open Polynomial Finset in
open Polynomial in
/-- M3b (Coleman): `g_n = n! · f_n` is irreducible over `ℚ`. -/
lemma sch_G_irreducible (n : ℕ) (hn : 1 ≤ n) : Irreducible (schG ℚ n) := by
  classical
  obtain ⟨hmon, hdeg⟩ := sch_G_monic n
  have hne : schG ℚ n ≠ 0 := hmon.ne_zero
  have hnu : ¬ IsUnit (schG ℚ n) := by
    intro hu; have := natDegree_eq_zero_of_isUnit hu; omega
  obtain ⟨h, hirr, hdvd⟩ := WfDvdMonoid.exists_irreducible_factor hnu hne
  set h₁ := h * C h.leadingCoeff⁻¹
  have hh0 : h ≠ 0 := hirr.ne_zero
  have h₁mon : h₁.Monic := monic_mul_leadingCoeff_inv hh0
  have h₁dvd : h₁ ∣ schG ℚ n := by
    refine dvd_trans ⟨C h.leadingCoeff, ?_⟩ hdvd
    rw [mul_assoc, ← C_mul, inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr hh0), C_1, mul_one]
  have hunit : IsUnit (C h.leadingCoeff⁻¹) :=
    isUnit_C.mpr (IsUnit.mk0 _ (inv_ne_zero (leadingCoeff_ne_zero.mpr hh0)))
  have h₁irr : Irreducible h₁ := (associated_mul_unit_right h _ hunit).irreducible hirr
  set d := h₁.natDegree
  have hd0 : d ≠ 0 := (natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible h₁irr)).ne'
  have hdle : d ≤ n := hdeg ▸ natDegree_le_of_dvd h₁dvd hne
  have hpart : ∀ p : ℕ, p.Prime → p ^ (n.factorization p) ∣ d := by
    intro p hp
    haveI := Fact.mk hp
    apply sch_deg_dvd_of_roots p (p ^ (n.factorization p)) d (h₁.map (algebraMap ℚ ℚ_[p]))
      (natDegree_map _) (h₁mon.map _)
    intro β hβ
    have hβh : aeval β h₁ = 0 := by rwa [aeval_map_algebraMap] at hβ
    have hβg : aeval β (schG ℚ n) = 0 := by
      obtain ⟨r, hr⟩ := h₁dvd; rw [hr, map_mul, hβh, zero_mul]
    rw [sch_aeval_G] at hβg
    obtain ⟨k, hdig, hnorm⟩ := sch_root_norm p n β hβg
    have hk : n.factorization p ≤ k := by
      by_contra hlt
      push Not at hlt
      have hdvdn : p ^ (k + 1) ∣ n := (pow_dvd_pow p hlt).trans (Nat.ordProj_dvd n p)
      apply hdig
      obtain ⟨c, hc⟩ := hdvdn
      rw [hc, pow_succ, mul_assoc, Nat.mul_div_cancel_left _ (pow_pos hp.pos k), Nat.mul_mod_right]
    exact (pow_dvd_pow p hk).trans (sch_level_dvd p β k hnorm)
  have hnd : n ∣ d := (Nat.factorization_prime_le_iff_dvd (by omega) hd0).mp
    (fun p hp => (hp.pow_dvd_iff_le_factorization hd0).mp (hpart p hp))
  have hdn : d = n := le_antisymm hdle (Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hnd)
  have hgh : schG ℚ n = h₁ := eq_of_monic_of_dvd_of_natDegree_le h₁mon hmon h₁dvd (by omega)
  rw [hgh]; exact h₁irr

open Polynomial Finset in
open Polynomial in
/-- For a prime `p` with `p ≤ n < 2p`, some root of `g_n` in `PadicAlgCl p` has level `1`. -/
lemma sch_level_one_root (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (hpn : p ≤ n) (hnp : n < 2 * p) :
    ∃ α : PadicAlgCl p, aeval α (schG ℚ n) = 0 ∧
      ‖α‖ = (p : ℝ) ^ (-((1 - ((p : ℝ) ^ 1)⁻¹) / ((p : ℝ) - 1))) := by
  classical
  have hp1 := hp.out.one_lt
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp1
  obtain ⟨hmon, hdeg⟩ := sch_G_monic n
  set gL := (schG ℚ n).map (algebraMap ℚ (PadicAlgCl p))
  have hsplit : gL.Splits := IsAlgClosed.splits _
  have hmonL : gL.Monic := hmon.map _
  -- every root has level 0 or 1
  have hlev : ∀ β ∈ gL.roots, ‖β‖ = 1 ∨
      ‖β‖ = (p : ℝ) ^ (-((1 - ((p : ℝ) ^ 1)⁻¹) / ((p : ℝ) - 1))) := by
    intro β hβ
    have hβ' : aeval β (schG ℚ n) = 0 := by
      have := (mem_roots hmonL.ne_zero).mp hβ
      rwa [IsRoot, eval_map_algebraMap] at this
    rw [sch_aeval_G] at hβ'
    obtain ⟨k, hdig, hnorm⟩ := sch_root_norm p n β hβ'
    have hk : k ≤ 1 := by
      by_contra hk; push Not at hk
      apply hdig
      have : n / p ^ k = 0 := Nat.div_eq_of_lt (lt_of_lt_of_le (by nlinarith [hp.out.two_le])
        (Nat.pow_le_pow_right hp.out.pos hk))
      rw [this, Nat.zero_mod]
    interval_cases k
    · left; rw [hnorm]; simp
    · right; exact hnorm
  by_contra hno
  push Not at hno
  have hall : ∀ β ∈ gL.roots, ‖β‖ = 1 := by
    intro β hβ
    rcases hlev β hβ with h | h
    · exact h
    · exfalso
      have hβ' : aeval β (schG ℚ n) = 0 := by
        have := (mem_roots hmonL.ne_zero).mp hβ
        rwa [IsRoot, eval_map_algebraMap] at this
      exact hno β hβ' h
  -- the product of the roots is `± n!`, of norm `p⁻¹`
  have hc0 := hsplit.coeff_zero_eq_prod_roots_of_monic hmonL
  have hcoef : gL.coeff 0 = (n.factorial : PadicAlgCl p) := by
    rw [coeff_map, show (schG ℚ n).coeff 0 = (n.factorial : ℚ) by
      rw [← sch_eval_zero_G ℚ n, coeff_zero_eq_eval_zero]]
    simp
  have hprod : ‖gL.roots.prod‖ = 1 := by
    have h1 : ‖gL.roots.prod‖ = (gL.roots.map (fun x => ‖x‖)).prod :=
      map_multiset_prod (normHom (α := PadicAlgCl p)) gL.roots
    rw [h1, Multiset.map_congr rfl hall, Multiset.map_const', Multiset.prod_replicate, one_pow]
  have hnorm1 : ‖(n.factorial : PadicAlgCl p)‖ = 1 := by
    rw [← hcoef, hc0, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, hprod]
  have hv : padicValNat p n.factorial = 1 := by
    rw [padicValNat_factorial (b := 2)]
    · simp only [Nat.Ico_succ_singleton, Finset.sum_singleton, pow_one]
      exact Nat.div_eq_of_lt_le (by omega) (by omega)
    · rw [Nat.log_lt_iff_lt_pow hp1 (by omega)]; nlinarith
  rw [sch_norm_natCast p _ (Nat.factorial_ne_zero n), hv, Nat.cast_one] at hnorm1
  have : (p : ℝ) ^ (-(1 : ℝ)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hpR (by norm_num)
  linarith

open Polynomial Finset in
open Polynomial in
/-- M3c (Coleman): for a prime `p` with `p ≤ n < 2p`, `p` divides the order of the Galois group of
`f` whenever `g_n = c · f`. -/
lemma sch_p_dvd_card_gal (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (hn : 1 ≤ n) (hpn : p ≤ n)
    (hnp : n < 2 * p) (f : ℚ[X]) (c : ℚ) (hc : c ≠ 0) (hf : schG ℚ n = C c * f) :
    p ∣ Nat.card f.Gal := by
  classical
  have hirr : Irreducible f := by
    have hg := sch_G_irreducible n hn
    rw [hf, mul_comm] at hg
    exact (associated_mul_unit_right f (C c) (isUnit_C.mpr (IsUnit.mk0 c hc))).irreducible_iff.mpr hg
  have hsep : f.Separable := hirr.separable
  have hf0 : f ≠ 0 := hirr.ne_zero
  set fp := f.map (algebraMap ℚ ℚ_[p])
  have hfp0 : fp ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap ℚ ℚ_[p]).injective).mpr hf0
  set E := IntermediateField.adjoin ℚ_[p] (fp.rootSet (PadicAlgCl p))
  haveI hspl : IsSplittingField ℚ_[p] E fp :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  haveI : FiniteDimensional ℚ_[p] E := IsSplittingField.finiteDimensional E fp
  haveI : IsGalois ℚ_[p] E := IsGalois.of_separable_splitting_field (p := fp) (hsep.map)
  -- a root of level 1
  obtain ⟨α, hα, hnorm⟩ := sch_level_one_root p n hpn hnp
  have hαf : aeval α f = 0 := by
    rw [hf, map_mul, aeval_C] at hα
    exact (mul_eq_zero.mp hα).resolve_left (by simpa using hc)
  have hαroot : α ∈ fp.rootSet (PadicAlgCl p) := by
    rw [mem_rootSet_of_ne hfp0, aeval_map_algebraMap]; exact hαf
  have hαE : α ∈ E := IntermediateField.subset_adjoin _ _ hαroot
  have hdvd1 : p ∣ Module.finrank ℚ_[p] E := by
    have h1 := sch_level_dvd p α 1 hnorm
    rw [pow_one, ← IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral α)] at h1
    exact h1.trans (IntermediateField.finrank_dvd_of_le_right
      (IntermediateField.adjoin_simple_le_iff.mpr hαE))
  rw [← IsGalois.card_aut_eq_finrank] at hdvd1
  -- restriction to the Galois group over `ℚ`
  have hsE : (f.map (algebraMap ℚ E)).Splits := by
    have := IsSplittingField.splits E fp
    rwa [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at this
  haveI : Fact (f.map (algebraMap ℚ E)).Splits := ⟨hsE⟩
  let ψ₀ : Gal(E/ℚ_[p]) →* f.Gal := (Gal.restrict f E).comp (AlgEquiv.restrictScalarsHom ℚ)
  have hroots : ∀ x : E, x ∈ fp.rootSet E → x ∈ f.rootSet E := by
    intro x hx
    rw [mem_rootSet_of_ne hfp0, aeval_map_algebraMap] at hx
    rw [mem_rootSet_of_ne hf0]; exact hx
  have hinj : Function.Injective ψ₀ := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    have hfix : Set.EqOn (σ.toAlgHom : E →ₐ[ℚ_[p]] E) (AlgHom.id ℚ_[p] E) (fp.rootSet E) := by
      intro x hx
      have h := Gal.restrict_smul (σ.restrictScalars ℚ) (⟨x, hroots x hx⟩ : f.rootSet E)
      have hσ' : Gal.restrict f E (σ.restrictScalars ℚ) = 1 := hσ
      rw [hσ', one_smul] at h
      exact h.symm
    have := AlgHom.ext_of_adjoin_eq_top (IsSplittingField.adjoin_rootSet E fp) hfix
    exact AlgEquiv.ext (fun x => congrArg (fun ψ : E →ₐ[ℚ_[p]] E => ψ x) this)
  have hcard : Nat.card Gal(E/ℚ_[p]) ∣ Nat.card f.Gal := by
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  exact hdvd1.trans hcard


open Polynomial Finset in
open MulAction Equiv Pointwise in
/-- M4a: a transitive permutation group containing a cycle of prime length `p` with `n < 2p` is
primitive. -/
lemma sch_isPreprimitive_of_long_cycle {α : Type*} [Fintype α] [DecidableEq α]
    (G : Subgroup (Perm α)) [IsPretransitive G α] {g : Perm α} (hg : g.IsCycle) (hgG : g ∈ G)
    (hp : g.support.card.Prime) (hn : Fintype.card α < 2 * g.support.card) :
    IsPreprimitive G α := by
  set p := g.support.card
  set γ : G := ⟨g, hgG⟩
  have hγord : orderOf γ = p := by
    rw [Subgroup.orderOf_mk, hg.orderOf]
  refine IsPreprimitive.mk (fun {B} hB => ?_)
  by_cases hsub : B.Subsingleton
  · exact Or.inl hsub
  right
  obtain ⟨y, hy, z, hz, hyz⟩ := Set.not_subsingleton_iff.mp hsub
  have hB2 : 2 ≤ B.ncard := by
    rw [← Set.ncard_pair hyz]
    exact Set.ncard_le_ncard (fun w hw => by rcases hw with rfl | rfl <;> assumption) (Set.toFinite _)
  -- a translate `B'` of `B` meets the support of `g`
  obtain ⟨x, hx⟩ : ∃ x, g x ≠ x := by
    by_contra h; push Not at h
    have : g = 1 := Perm.ext h
    exact hg.ne_one this
  obtain ⟨k, hk⟩ := exists_smul_eq G y x
  set B' := k • B with hB'def
  have hB'block : IsBlock G B' := hB.translate k
  have hxB' : x ∈ B' := ⟨y, hy, hk⟩
  have hB'card : B'.ncard = B.ncard := Set.ncard_smul_set k B
  -- `γ` stabilizes `B'`
  have hstab : γ • B' = B' := by
    by_contra hne
    -- the `⟨γ⟩`-orbit of `B'` has `p` elements
    set H := Subgroup.zpowers γ
    have hHcard : Nat.card H = p := by rw [Nat.card_zpowers, hγord]
    have hdvd : (orbit H B').ncard ∣ p := by
      rw [← index_stabilizer, ← hHcard]; exact Subgroup.index_dvd_card _
    have hne1 : (orbit H B').ncard ≠ 1 := by
      intro h1
      obtain ⟨C, hC⟩ := Set.ncard_eq_one.mp h1
      have h1' : (⟨γ, Subgroup.mem_zpowers γ⟩ : H) • B' ∈ orbit H B' := mem_orbit _ _
      have h2' : B' ∈ orbit H B' := mem_orbit_self _
      rw [hC] at h1' h2'
      exact hne (h1'.trans h2'.symm)
    have horb : (orbit H B').ncard = p := by
      rcases (Nat.dvd_prime hp).mp hdvd with h | h
      · exact absurd h hne1
      · exact h
    have hsubset : orbit H B' ⊆ orbit G B' := by
      rintro C ⟨h, rfl⟩; exact ⟨h.1, rfl⟩
    have hGorb : p ≤ (orbit G B').ncard := by
      rw [← horb]; exact Set.ncard_le_ncard hsubset (Set.toFinite _)
    have hcount := hB'block.ncard_block_mul_ncard_orbit_eq ⟨x, hxB'⟩
    rw [Nat.card_eq_fintype_card, hB'card] at hcount
    nlinarith
  -- so the support of `g` lies in `B'`
  have hsupp : (g.support : Set α) ⊆ B' := by
    intro w hw
    rw [Finset.mem_coe, Perm.mem_support] at hw
    obtain ⟨i, hi⟩ := hg.exists_zpow_eq hx hw
    have hmem : γ ^ i ∈ stabilizer G B' := Subgroup.zpow_mem _ hstab i
    rw [mem_stabilizer_iff] at hmem
    rw [← hmem, ← hi]
    exact ⟨x, hxB', by simp [γ, Subgroup.coe_zpow]⟩
  have hcardB' : p ≤ B'.ncard := by
    have := Set.ncard_le_ncard hsupp (Set.toFinite _)
    rwa [Set.ncard_coe_finset] at this
  apply hB.eq_univ_of_card_lt
  rw [Nat.card_eq_fintype_card]
  omega


/-!
Port of Jordan's theorem for a cycle of prime length (Wielandt 13.9) and its helper lemmas from
the Tau Ceti project, PR #8945 (https://github.com/TauCetiProject/TauCeti/pull/8945), files
`TauCeti/GroupTheory/Perm/Jordan.lean`, `TauCeti/GroupTheory/Sylow.lean`,
`TauCeti/GroupTheory/Commutator.lean`, `TauCeti/GroupTheory/Perm/Basic.lean`,
`TauCeti/Data/Nat/Factorial/Prime.lean`.
Copyright (c) 2026 The Tau Ceti contributors. Released under the Apache 2.0 license.
Changes: declarations renamed to start with `sch_`, moved out of the `TauCeti` namespace,
visibility modifiers removed, `open ... in` per declaration; mathematical content unchanged.
-/

open Polynomial Finset in
open MulAction Equiv Pointwise in
open Equiv Equiv.Perm in
theorem sch_not_sq_dvd_factorial {p : ℕ} (hp : p.Prime) : ¬ p ^ 2 ∣ p.factorial := by
  intro h
  rw [← Nat.mul_factorial_pred hp.ne_zero, pow_two] at h
  have := hp.dvd_factorial.1 (Nat.dvd_of_mul_dvd_mul_left hp.pos h)
  exact (Nat.not_le_of_gt (Nat.sub_lt hp.pos (by omega))) this

open Polynomial Finset in
open MulAction Equiv Pointwise in
theorem sch_swap_apply_notMem {α : Type*} [DecidableEq α] {s : Finset α} {a b z : α}
    (ha : a ∉ s) (hb : b ∉ s) (hz : z ∉ s) : Equiv.swap a b z ∉ s := by
  rw [Equiv.swap_apply_def]; split_ifs <;> assumption

open Polynomial Finset in
open MulAction Equiv Pointwise in
open Equiv Equiv.Perm in
theorem sch_exists_mul_zpow_inv_apply_eq_of_commute {α : Type*} [Fintype α] [DecidableEq α]
    {g t : Perm α} (hgc : g.IsCycle) (htg : Commute t g) :
    ∃ j : ℤ, (∀ z ∈ g.support, (t * (g ^ j)⁻¹) z = z) ∧
      (∀ z ∉ g.support, (t * (g ^ j)⁻¹) z = t z) := by
  obtain ⟨hts, j, hj⟩ := hgc.commute_iff.1 htg
  refine ⟨j, ?_, ?_⟩
  · intro z hz
    have hw : (g ^ j)⁻¹ z ∈ g.support := by rwa [← zpow_neg, zpow_apply_mem_support]
    rw [Perm.mul_apply, ← ofSubtype_subtypePerm_of_mem hts hw, ← hj, ← Perm.mul_apply,
      mul_inv_cancel, Perm.one_apply]
  · intro z hz
    rw [Perm.mul_apply, Perm.inv_eq_iff_eq.2 (zpow_apply_eq_self_of_apply_eq_self
      (notMem_support.1 hz) j).symm]

open Polynomial Finset in
open MulAction Equiv Pointwise in
open Subgroup in
open scoped commutatorElement in
theorem sch_commute_commutatorElement_of_inv_mul_mul_mem_zpowers {G : Type*} [Group G] {g x y : G}
    (hx : x⁻¹ * g * x ∈ zpowers g) (hy : y⁻¹ * g * y ∈ zpowers g) : Commute ⁅x, y⁆ g := by
  obtain ⟨i, hi⟩ := mem_zpowers_iff.1 hx
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hy
  have hpow : ∀ (z : G) (m : ℤ), z⁻¹ * g ^ m * z = (z⁻¹ * g * z) ^ m := fun z m ↦ by
    simpa using (conj_zpow (a := z⁻¹) (b := g) (i := m)).symm
  have hxk : x⁻¹ * g ^ k * x = g ^ (i * k) := by
    rw [hpow, ← hi, ← zpow_mul]
  have hyi : y⁻¹ * g ^ i * y = g ^ (i * k) := by
    rw [hpow, ← hk, ← zpow_mul, mul_comm i k]
  have key : (y * x)⁻¹ * g * (y * x) = (x * y)⁻¹ * g * (x * y) := by
    calc (y * x)⁻¹ * g * (y * x) = x⁻¹ * (y⁻¹ * g * y) * x := by group
      _ = g ^ (i * k) := by rw [← hk, hxk]
      _ = y⁻¹ * (x⁻¹ * g * x) * y := by rw [← hi, hyi]
      _ = (x * y)⁻¹ * g * (x * y) := by group
  rw [commute_iff_eq, commutatorElement_def]
  calc x * y * x⁻¹ * y⁻¹ * g = x * y * ((y * x)⁻¹ * g * (y * x)) * (y * x)⁻¹ := by group
    _ = x * y * ((x * y)⁻¹ * g * (x * y)) * (y * x)⁻¹ := by rw [key]
    _ = g * (x * y * x⁻¹ * y⁻¹) := by group

open Polynomial Finset in
open MulAction Equiv Pointwise in
theorem sch_sylow_card_eq_of_dvd_of_not_sq_dvd {G : Type*} [Group G] [Finite G] {p : ℕ}
    [hp : Fact p.Prime] (P : Sylow p G) (hdvd : p ∣ Nat.card G)
    (hsq : ¬ p ^ 2 ∣ Nat.card G) : Nat.card P = p := by
  have hG : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have h1 := (hp.out.dvd_iff_one_le_factorization hG).1 hdvd
  have h2 := mt (hp.out.pow_dvd_iff_le_factorization (k := 2) hG).2 hsq
  have hfac : (Nat.card G).factorization p = 1 := by omega
  rw [P.card_eq_multiplicity, hfac, pow_one]

open Polynomial Finset in
open MulAction Equiv Pointwise in
theorem sch_exists_mul_mul_inv_mem_zpowers_of_not_sq_dvd {G : Type*} [Group G] [Finite G] {p : ℕ}
    [hp : Fact p.Prime] (hsq : ¬ p ^ 2 ∣ Nat.card G) {g h : G}
    (hg : orderOf g = p) (hh : orderOf h = p) : ∃ y : G, y * h * y⁻¹ ∈ Subgroup.zpowers g := by
  obtain ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
  have hcard : p ^ (Nat.card G).factorization p = p := by
    rw [← P.card_eq_multiplicity,
      sch_sylow_card_eq_of_dvd_of_not_sq_dvd P (hg ▸ orderOf_dvd_natCard g) hsq]
  let Pg := Sylow.ofCard (Subgroup.zpowers g) (by rw [Nat.card_zpowers, hcard, hg])
  let Ph := Sylow.ofCard (Subgroup.zpowers h) (by rw [Nat.card_zpowers, hcard, hh])
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq G Ph Pg
  refine ⟨y, ?_⟩
  have hmem : y * h * y⁻¹ ∈ ((y • Ph : Sylow p G) : Subgroup G) := by
    rw [Sylow.coe_subgroup_smul, ← MulAut.conj_apply]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (by
      simp only [Ph, Sylow.coe_ofCard]
      exact Subgroup.mem_zpowers h)
  rw [hy] at hmem
  simp only [Pg, Sylow.coe_ofCard] at hmem
  exact hmem

open Polynomial Finset in
open MulAction Equiv Pointwise in
open MulAction Equiv Equiv.Perm Finset Subgroup in
open scoped commutatorElement in
/-- **Jordan's multiple primitivity for a cycle of prime length.** A primitive permutation group
containing a cycle `g` of prime length is `(k + 1)`-fold primitive, where `k` is the number of
fixed points of `g`. -/
theorem sch_isMultiplyPreprimitive_of_isCycle_mem {α : Type*} [Fintype α] [DecidableEq α] {G : Subgroup (Perm α)} (hG : IsPreprimitive G α) {g : Perm α}
    (hgc : g.IsCycle) (hgp : (#g.support).Prime) (hg : g ∈ G) :
    IsMultiplyPreprimitive G α (#g.supportᶜ + 1) := by
  classical
  obtain hk | hk := Nat.eq_zero_or_pos #g.supportᶜ
  · rwa [hk, zero_add, is_one_preprimitive_iff]
  obtain ⟨m, hm⟩ : ∃ m, #g.supportᶜ = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hk).symm⟩
  have hcard := (card_compl_add_card g.support).trans Nat.card_eq_fintype_card.symm
  have hp2 := hgp.two_le
  rw [hm]
  refine hG.isMultiplyPreprimitive (s := (g.support : Set α)ᶜ) ?_ (by omega) ?_
  · rw [← coe_compl, Set.ncard_coe_finset, hm]
  · -- The subgroup fixing the complement of the support is transitive on a set of prime size.
    have := isPretransitive_of_isCycle_mem hgc hg
    apply IsPreprimitive.of_prime_card
    convert hgp using 1
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext x
    simp [SubMulAction.mem_ofFixingSubgroup_iff]

open Polynomial Finset in
open MulAction Equiv Pointwise in
open MulAction Equiv Equiv.Perm Finset Subgroup in
open scoped commutatorElement in
/-- The Frattini step: if `x ∈ G` preserves the support of a cycle `g ∈ G` of prime length, then
`x` can be corrected by an element of `G` supported on the support of `g` so that it normalizes
`⟨g⟩`. The subgroup of `G` supported on the support of `g` has `⟨g⟩` as a Sylow subgroup. -/
theorem sch_exists_eqOn_compl_support_mul_mul_inv_mem_zpowers {α : Type*} [Fintype α] [DecidableEq α] {G : Subgroup (Perm α)} {g x : Perm α}
    (hgc : g.IsCycle) (hgp : (#g.support).Prime) (hg : g ∈ G) (hx : x ∈ G)
    (hxs : ∀ z, x z ∈ g.support ↔ z ∈ g.support) :
    ∃ n ∈ G, (∀ z ∉ g.support, n z = x z) ∧ n * g * n⁻¹ ∈ zpowers g := by
  have := Fact.mk hgp
  -- The elements of `G` supported on the support of `g`.
  let F : Subgroup (Perm α) := G ⊓ (ofSubtype : Perm {z // z ∈ g.support} →* Perm α).range
  have hmemF : ∀ σ ∈ G, (∀ z, σ z ≠ z → z ∈ g.support) → σ ∈ F := fun σ hσ hsupp ↦
    ⟨hσ, mem_range_ofSubtype_iff.2 fun z hz ↦ hsupp z (mem_support.1 hz)⟩
  have hgF : g ∈ F := hmemF g hg fun z hz ↦ mem_support.2 hz
  have hg'F : x * g * x⁻¹ ∈ F := by
    refine hmemF _ (mul_mem (mul_mem hx hg) (inv_mem hx)) fun z hz ↦ ?_
    have h : x⁻¹ z ∈ g.support := by
      rw [mem_support]
      intro h
      apply hz
      rw [Perm.mul_apply, Perm.mul_apply, h]
      exact x.apply_symm_apply z
    simpa using (hxs _).2 h
  -- `F` embeds into the symmetric group on the support of `g`, so `p ^ 2` does not divide `|F|`.
  have hsq : ¬ (#g.support) ^ 2 ∣ Nat.card F := by
    intro h
    have hcard : Nat.card F ∣ (#g.support).factorial := by
      refine (card_dvd_of_le inf_le_right).trans (dvd_of_eq ?_)
      rw [← Nat.card_congr (MonoidHom.ofInjective ofSubtype_injective).toEquiv, Nat.card_perm,
        Nat.card_eq_fintype_card, Fintype.card_coe]
    exact sch_not_sq_dvd_factorial hgp (h.trans hcard)
  obtain ⟨y, hy⟩ := sch_exists_mul_mul_inv_mem_zpowers_of_not_sq_dvd hsq
    (g := ⟨g, hgF⟩) (h := ⟨x * g * x⁻¹, hg'F⟩) (by rw [orderOf_mk, hgc.orderOf])
    (by rw [orderOf_mk, hgc.conj.orderOf, card_support_conj])
  refine ⟨y * x, mul_mem y.2.1 hx, fun z hz ↦ ?_, ?_⟩
  · have hyz : (y : Perm α) (x z) = x z := by
      by_contra h
      exact hz ((hxs z).1 (by simpa using mem_range_ofSubtype_iff.1 y.2.2 (mem_support.2 h)))
    rw [Perm.mul_apply, hyz]
  · obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hy
    refine mem_zpowers_iff.2 ⟨k, ?_⟩
    simpa only [Subgroup.coe_zpow, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, mul_assoc] using
      congrArg Subtype.val hk

open Polynomial Finset in
open MulAction Equiv Pointwise in
open MulAction Equiv Equiv.Perm Finset Subgroup in
open scoped commutatorElement in
/-- If `G` is `k`-fold transitive, where `k` is the number of fixed points of a cycle `g ∈ G` of
prime length, then every transposition of two fixed points of `g` is induced on the fixed points
of `g` by an element of `G` normalizing `⟨g⟩`. -/
theorem sch_exists_eqOn_swap_mul_mul_inv_mem_zpowers {α : Type*} [Fintype α] [DecidableEq α] {G : Subgroup (Perm α)} {g : Perm α} (hgc : g.IsCycle)
    (hgp : (#g.support).Prime) (hg : g ∈ G) (hG : IsMultiplyPretransitive G α #g.supportᶜ)
    {a b : α} (ha : a ∉ g.support) (hb : b ∉ g.support) :
    ∃ n ∈ G, (∀ z ∉ g.support, n z = swap a b z) ∧ n * g * n⁻¹ ∈ zpowers g := by
  have hswap : ∀ z ∉ g.support, swap a b z ∉ g.support := fun _ ↦ sch_swap_apply_notMem ha hb
  -- Realize the transposition on the fixed points of `g` by `k`-fold transitivity.
  let e : Fin #g.supportᶜ ↪ α :=
    g.supportᶜ.equivFin.symm.toEmbedding.trans (Function.Embedding.subtype _)
  obtain ⟨x, hx⟩ := exists_smul_eq G e (e.trans (swap a b).toEmbedding)
  have hxΔ : ∀ z ∉ g.support, (x : Perm α) z = swap a b z := fun z hz ↦ by
    simpa only [e, Function.Embedding.smul_apply, Function.Embedding.trans_apply,
      Function.Embedding.subtype_apply, Equiv.toEmbedding_apply, Equiv.symm_apply_apply,
      Subgroup.smul_def, Perm.smul_def] using
      DFunLike.congr_fun hx (g.supportᶜ.equivFin ⟨z, mem_compl.2 hz⟩)
  have hxs : ∀ z, (x : Perm α) z ∈ g.support ↔ z ∈ g.support := fun z ↦ by
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · by_contra hz
      exact hswap z hz (hxΔ z hz ▸ h)
    · by_contra hxz
      have hw := hswap _ hxz
      have : (x : Perm α) (swap a b ((x : Perm α) z)) = (x : Perm α) z := by
        rw [hxΔ _ hw, swap_apply_self]
      exact hw (by rwa [(x : Perm α).injective this])
  obtain ⟨n, hnG, hn, hng⟩ := sch_exists_eqOn_compl_support_mul_mul_inv_mem_zpowers hgc hgp hg x.2 hxs
  exact ⟨n, hnG, fun z hz ↦ (hn z hz).trans (hxΔ z hz), hng⟩

open Polynomial Finset in
open MulAction Equiv Pointwise in
open MulAction Equiv Equiv.Perm Finset Subgroup in
open scoped commutatorElement in
/-- **Jordan's theorem for a cycle of prime length** (Wielandt, Theorem 13.9). A primitive
permutation group of degree at least `p + 3` that contains a cycle of prime length `p` contains
the alternating group. -/
theorem sch_alternatingGroup_le_of_isPreprimitive_of_isCycle_mem {α : Type*} [Fintype α] [DecidableEq α] {G : Subgroup (Perm α)} (hG : IsPreprimitive G α) {p : ℕ}
    (hp : p.Prime) (hp' : p + 3 ≤ Nat.card α) {g : Perm α} (hgc : g.IsCycle)
    (hgp : #g.support = p) (hg : g ∈ G) : alternatingGroup α ≤ G := by
  subst hgp
  have hcard := (card_compl_add_card g.support).trans Nat.card_eq_fintype_card.symm
  have htr : IsMultiplyPretransitive G α #g.supportᶜ := by
    have := (sch_isMultiplyPreprimitive_of_isCycle_mem hG hgc hp hg).isMultiplyPretransitive
    exact isMultiplyPretransitive_of_le (n := #g.supportᶜ + 1) (by omega)
      (by have := hp.two_le; omega)
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := two_lt_card_iff.1 (by omega : 2 < #g.supportᶜ)
  rw [mem_compl] at ha hb hc
  obtain ⟨n₁, hn₁G, hn₁, hn₁g⟩ := sch_exists_eqOn_swap_mul_mul_inv_mem_zpowers hgc hp hg htr ha hb
  obtain ⟨n₂, hn₂G, hn₂, hn₂g⟩ := sch_exists_eqOn_swap_mul_mul_inv_mem_zpowers hgc hp hg htr hb hc
  have hinv : ∀ {n : Perm α} {x y : α}, (∀ z ∉ g.support, n z = swap x y z) → x ∉ g.support →
      y ∉ g.support → ∀ z ∉ g.support, n⁻¹ z = swap x y z := fun hn hx hy z hz ↦ by
    rw [Perm.inv_eq_iff_eq, hn _ (sch_swap_apply_notMem hx hy hz), swap_apply_self]
  -- The commutator `t` of `n₁⁻¹` and `n₂⁻¹` centralizes `g`, so it is a power of `g` on the
  -- support of `g`; on the fixed points of `g` it is the `3`-cycle `(a b)(b c)(a b)(b c)`.
  have htg : Commute ⁅n₁⁻¹, n₂⁻¹⁆ g :=
    sch_commute_commutatorElement_of_inv_mul_mul_mem_zpowers (x := n₁⁻¹) (y := n₂⁻¹)
      (by rwa [inv_inv]) (by rwa [inv_inv])
  obtain ⟨j, hfix, hout⟩ := sch_exists_mul_zpow_inv_apply_eq_of_commute hgc htg
  have hτ : ⁅n₁⁻¹, n₂⁻¹⁆ * (g ^ j)⁻¹ = swap c a * swap c b := by
    ext z
    by_cases hz : z ∈ g.support
    · rw [hfix z hz, Perm.mul_apply]
      have hne : ∀ d ∉ g.support, z ≠ d := fun d hd h ↦ hd (h ▸ hz)
      rw [swap_apply_of_ne_of_ne (hne c hc) (hne b hb),
        swap_apply_of_ne_of_ne (hne c hc) (hne a ha)]
    · have hperm : swap a b * swap b c * swap a b * swap b c = swap c a * swap c b := by
        rw [swap_comm a b, swap_comm b c, swap_mul_swap_mul_swap hbc.symm hac.symm, swap_comm a c]
      rw [← hperm, hout z hz, commutatorElement_def, inv_inv, inv_inv]
      simp only [Perm.mul_apply]
      have h₁ := sch_swap_apply_notMem hb hc hz
      have h₂ := sch_swap_apply_notMem ha hb h₁
      rw [hn₂ z hz, hn₁ _ h₁, hinv hn₂ hb hc _ h₂, hinv hn₁ ha hb _ (sch_swap_apply_notMem hb hc h₂)]
  refine alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hG
    (isThreeCycle_swap_mul_swap_same hac.symm hbc.symm hab) (hτ ▸ ?_)
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem (mul_mem (inv_mem hn₁G) (inv_mem hn₂G)) (inv_mem (inv_mem hn₁G)))
    (inv_mem (inv_mem hn₂G))) (inv_mem (zpow_mem hg j))


/-
Module M5 (`sch_real_main_inequality`, `sch_main_inequality`, `sch_centralBinom_le`,
`sch_exists_prime_mid`) is adapted from the proof of Bertrand's postulate in Mathlib,
`Mathlib/NumberTheory/Bertrand.lean`
(https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/NumberTheory/Bertrand.lean).
Copyright (c) 2020 Patrick Stevens. Authors: Patrick Stevens, Bolton Bailey.
Released under the Apache 2.0 license.
Changes:
* `sch_real_main_inequality` follows `Bertrand.real_main_inequality` (concavity of
  `log x + √(2x) log (2x) - (log 4 / 3) x`), with the extra factor `(2x)^3`, i.e. exponent
  `√(2x) + 3`, the threshold `2048` instead of `512`, and an extra concave summand `3 log (2x)`.
* `sch_main_inequality` is the natural-number form, as `bertrand_main_inequality`.
* `sch_centralBinom_le` follows `centralBinom_le_of_no_bertrand_prime`; the part bounding the
  primes up to `2m/3` is copied, and the hypothesis "no prime in `(m, 2m]`" is replaced by
  "the primes of `(m, 2m]` lie in a set `T` of at most three numbers", which adds the factor
  `(2m)^3`.
* `sch_exists_prime_mid` (a prime `p` with `n < 2p` and `p + 3 ≤ n` for `n ≥ 8`) is new; its
  small cases use a chain of primes in the style of `Nat.exists_prime_lt_and_le_two_mul`.
-/

open Polynomial Finset in
open MulAction Equiv Pointwise in
open Real in
/-- M5b: `x (2x)^{√(2x) + 3} 4^{2x/3} ≤ 4^x` for `x ≥ 2048`. -/
theorem sch_real_main_inequality {x : ℝ} (x_large : (2048 : ℝ) ≤ x) :
    x * (2 * x) ^ (√(2 * x) + 3) * 4 ^ (2 * x / 3) ≤ 4 ^ x := by
  let f : ℝ → ℝ := fun x => log x + (√(2 * x) + 3) * log (2 * x) - log 4 / 3 * x
  have hf' : ∀ x, 0 < x → 0 < x * (2 * x) ^ (√(2 * x) + 3) / 4 ^ (x / 3) := fun x h =>
    div_pos (mul_pos h (rpow_pos_of_pos (mul_pos two_pos h) _)) (rpow_pos_of_pos four_pos _)
  have hf : ∀ x, 0 < x → f x = log (x * (2 * x) ^ (√(2 * x) + 3) / 4 ^ (x / 3)) := by
    intro x h5
    have h6 := mul_pos (zero_lt_two' ℝ) h5
    have h7 := rpow_pos_of_pos h6 (√(2 * x) + 3)
    rw [log_div (mul_pos h5 h7).ne' (rpow_pos_of_pos four_pos _).ne', log_mul h5.ne' h7.ne',
      log_rpow h6, log_rpow zero_lt_four, ← mul_div_right_comm, ← mul_div, mul_comm x]
  have h5 : 0 < x := lt_of_lt_of_le (by norm_num1) x_large
  rw [← div_le_one (rpow_pos_of_pos four_pos x), ← div_div_eq_mul_div, ← rpow_sub four_pos, ←
    mul_div 2 x, mul_div_left_comm, ← mul_one_sub, (by norm_num1 : (1 : ℝ) - 2 / 3 = 1 / 3),
    mul_one_div, ← log_nonpos_iff (hf' x h5).le, ← hf x h5]
  have h : ConcaveOn ℝ (Set.Ioi 0.5) f := by
    have hlog2 : ConcaveOn ℝ (Set.Ioi (0.5 : ℝ)) (fun x : ℝ => log (2 * x)) := by
      refine ((concaveOn_const (log 2) (convex_Ioi (0.5 : ℝ))).add
        (strictConcaveOn_log_Ioi.concaveOn.subset (Set.Ioi_subset_Ioi (by norm_num))
          (convex_Ioi 0.5))).congr ?_
      intro x hx
      have hx0 : x ≠ 0 := by
        have : (0.5 : ℝ) < x := hx
        exact ne_of_gt (lt_trans (by norm_num) this)
      show log 2 + log x = log (2 * x)
      rw [log_mul two_ne_zero hx0]
    have hsq : ConcaveOn ℝ (Set.Ioi (0.5 : ℝ)) (fun x : ℝ => √(2 * x) * log (2 * x)) := by
      convert! ((strictConcaveOn_sqrt_mul_log_Ioi.concaveOn.comp_linearMap
        ((2 : ℝ) • LinearMap.id))) using 1
      ext x
      simp only [Set.mem_Ioi, Set.mem_preimage, LinearMap.smul_apply,
        LinearMap.id_coe, id_eq, smul_eq_mul]
      rw [← mul_lt_mul_iff_right₀ (two_pos)]
      norm_num1
      rfl
    have hsum : ConcaveOn ℝ (Set.Ioi (0.5 : ℝ))
        (fun x : ℝ => log x + (√(2 * x) + 3) * log (2 * x)) := by
      have : (fun x : ℝ => log x + (√(2 * x) + 3) * log (2 * x)) =
          fun x => log x + (√(2 * x) * log (2 * x) + 3 * log (2 * x)) := by
        ext x; ring
      rw [this]
      exact (strictConcaveOn_log_Ioi.concaveOn.subset (Set.Ioi_subset_Ioi (by norm_num))
        (convex_Ioi 0.5)).add (hsq.add (hlog2.smul (by norm_num : (0 : ℝ) ≤ 3)))
    apply hsum.sub
    apply ConvexOn.smul
    · refine div_nonneg (log_nonneg (by norm_num1)) (by norm_num1)
    · exact convexOn_id (convex_Ioi (0.5 : ℝ))
  suffices ∃ x1 x2, 0.5 < x1 ∧ x1 < x2 ∧ x2 ≤ x ∧ 0 ≤ f x1 ∧ f x2 ≤ 0 by
    obtain ⟨x1, x2, h1, h2, h0, h3, h4⟩ := this
    exact (h.right_le_of_le_left'' h1 ((h1.trans h2).trans_le h0) h2 h0 (h4.trans h3)).trans h4
  refine ⟨18, 2048, by norm_num1, by norm_num1, x_large, ?_, ?_⟩
  · have : √(2 * 18 : ℝ) = 6 := (sqrt_eq_iff_mul_self_eq_of_pos (by norm_num1)).mpr (by norm_num1)
    rw [hf _ (by norm_num1), log_nonneg_iff (by positivity), this, one_le_div (by positivity)]
    rw [show (6 : ℝ) + 3 = ((9 : ℕ) : ℝ) by norm_num, rpow_natCast,
      show (18 : ℝ) / 3 = ((6 : ℕ) : ℝ) by norm_num, rpow_natCast]
    norm_num
  · have : √(2 * 2048 : ℝ) = 64 :=
      (sqrt_eq_iff_mul_self_eq_of_pos (by norm_num1)).mpr (by norm_num1)
    rw [hf _ (by norm_num1), log_nonpos_iff (hf' _ (by norm_num1)).le, this,
      div_le_one (by positivity)]
    rw [show (64 : ℝ) + 3 = ((67 : ℕ) : ℝ) by norm_num, rpow_natCast]
    rw [show (2 * 2048 : ℝ) = 2 ^ (12 : ℕ) by norm_num, show (2048 : ℝ) = 2 ^ (11 : ℕ) by norm_num,
      ← pow_mul, ← pow_add, show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← rpow_mul (by norm_num),
      ← rpow_natCast]
    apply rpow_le_rpow_of_exponent_le (by norm_num)
    norm_num

open Polynomial Finset in
open MulAction Equiv Pointwise in
open Nat in
theorem sch_main_inequality {n : ℕ} (n_large : 2048 ≤ n) :
    n * ((2 * n) ^ sqrt (2 * n) * 4 ^ (2 * n / 3) * (2 * n) ^ 3) ≤ 4 ^ n := by
  have key := sch_real_main_inequality (x := n) (by exact_mod_cast n_large)
  have h2n : (1 : ℝ) ≤ 2 * n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    linarith
  have h1 : (2 * (n : ℝ)) ^ (sqrt (2 * n)) * (2 * n) ^ 3 ≤ (2 * n) ^ (Real.sqrt (2 * n) + 3) := by
    rw [← pow_add, ← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le h2n
    push_cast
    have := Real.nat_sqrt_le_real_sqrt (a := 2 * n)
    push_cast at this
    linarith
  have h2 : (4 : ℝ) ^ (2 * n / 3) ≤ (4 : ℝ) ^ (2 * (n : ℝ) / 3) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    exact cast_div_le.trans (by norm_cast)
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hR : (n : ℝ) * ((2 * (n : ℝ)) ^ sqrt (2 * n) * (4 : ℝ) ^ (2 * n / 3) *
      (2 * (n : ℝ)) ^ 3) ≤ (4 : ℝ) ^ (n : ℝ) := by
    calc (n : ℝ) * ((2 * (n : ℝ)) ^ sqrt (2 * n) * (4 : ℝ) ^ (2 * n / 3) * (2 * (n : ℝ)) ^ 3)
        = (n : ℝ) * ((2 * (n : ℝ)) ^ sqrt (2 * n) * (2 * (n : ℝ)) ^ 3) *
            (4 : ℝ) ^ (2 * n / 3) := by ring
      _ ≤ (n : ℝ) * (2 * (n : ℝ)) ^ (Real.sqrt (2 * n) + 3) * (4 : ℝ) ^ (2 * (n : ℝ) / 3) := by
          gcongr
      _ ≤ (4 : ℝ) ^ (n : ℝ) := key
  rw [Real.rpow_natCast] at hR
  exact_mod_cast hR

open Polynomial Finset in
open MulAction Equiv Pointwise in
open Nat in
/-- M5a: if the primes of `(m, 2m]` lie in a set `T` of at most three numbers `≤ 2m`, then
`C(2m, m) ≤ (2m)^{√(2m)} 4^{2m/3} (2m)^3` (adapted from Mathlib's
`centralBinom_le_of_no_bertrand_prime`). -/
theorem sch_centralBinom_le (m : ℕ) (m_large : 2 < m) (T : Finset ℕ) (hT : T.card ≤ 3)
    (hTle : ∀ x ∈ T, x ≤ 2 * m) (hprime : ∀ p : ℕ, p.Prime → m < p → p ≤ 2 * m → p ∈ T) :
    centralBinom m ≤ (2 * m) ^ sqrt (2 * m) * 4 ^ (2 * m / 3) * (2 * m) ^ 3 := by
  classical
  have m_pos : 0 < m := (Nat.zero_le _).trans_lt m_large
  have m2_pos : 1 ≤ 2 * m := mul_pos (zero_lt_two' ℕ) m_pos
  let f x := x ^ m.centralBinom.factorization x
  have hsplit : centralBinom m = (∏ x ∈ Finset.range (2 * m / 3 + 1), f x) *
      ∏ x ∈ Finset.Ico (2 * m / 3 + 1) (2 * m + 1), f x := by
    rw [Finset.prod_range_mul_prod_Ico _ (by omega)]
    exact (prod_pow_factorization_centralBinom m).symm
  rw [hsplit]
  apply mul_le_mul'
  · -- the small primes, exactly as in Mathlib's proof of Bertrand's postulate
    let S := {p ∈ Finset.range (2 * m / 3 + 1) | Nat.Prime p}
    have : ∏ x ∈ S, f x = ∏ x ∈ Finset.range (2 * m / 3 + 1), f x := by
      refine Finset.prod_filter_of_ne fun p _ h => ?_
      contrapose h; dsimp only [f]
      rw [factorization_eq_zero_of_not_prime m.centralBinom h, _root_.pow_zero]
    rw [← this, ← Finset.prod_filter_mul_prod_filter_not S (· ≤ sqrt (2 * m))]
    apply mul_le_mul'
    · refine (Finset.prod_le_prod' fun p _ => (?_ : f p ≤ 2 * m)).trans ?_
      · exact pow_factorization_choose_le (mul_pos two_pos m_pos)
      have : (Finset.Icc 1 (sqrt (2 * m))).card = sqrt (2 * m) := by
        rw [card_Icc, Nat.add_sub_cancel]
      rw [Finset.prod_const]
      refine pow_right_mono₀ m2_pos ((Finset.card_le_card fun x hx => ?_).trans this.le)
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.1 h1).2.one_lt.le, h2⟩
    · refine le_trans ?_ (primorial_le_four_pow (2 * m / 3))
      refine (Finset.prod_le_prod' fun p hp => (?_ : f p ≤ p)).trans ?_
      · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
        refine (pow_right_mono₀ (Finset.mem_filter.1 h1).2.one_lt.le ?_).trans (pow_one p).le
        exact Nat.factorization_choose_le_one (sqrt_lt'.mp <| not_le.1 h2)
      refine Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset (fun p => ¬ p ≤ sqrt (2 * m)) S) ?_
      exact fun p hp _ => (Finset.mem_filter.1 hp).2.one_lt.le
  · -- the large primes: only those in `T` contribute, each at most `2m`
    have hbound : ∀ x ∈ Finset.Ico (2 * m / 3 + 1) (2 * m + 1),
        f x ≤ if x ∈ T then 2 * m else 1 := by
      intro x hx
      rw [Finset.mem_Ico] at hx
      dsimp only [f]
      by_cases hxp : x.Prime
      · by_cases hxm : x ≤ m
        · rw [factorization_centralBinom_of_two_mul_self_lt_three_mul m_large hxm (by omega),
            _root_.pow_zero]
          split_ifs <;> omega
        · have hxT := hprime x hxp (by omega) (by omega)
          rw [if_pos hxT]
          have hle1 : m.centralBinom.factorization x ≤ 1 :=
            Nat.factorization_choose_le_one (by nlinarith)
          calc x ^ m.centralBinom.factorization x ≤ x ^ 1 :=
                pow_right_mono₀ hxp.one_lt.le hle1
            _ ≤ 2 * m := by rw [pow_one]; omega
      · rw [factorization_eq_zero_of_not_prime _ hxp, _root_.pow_zero]
        split_ifs <;> omega
    refine (Finset.prod_le_prod' hbound).trans ?_
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    refine pow_right_mono₀ m2_pos ?_
    exact (Finset.card_le_card (fun x hx => (Finset.mem_filter.1 hx).2)).trans hT

open Polynomial Finset in
open MulAction Equiv Pointwise in
open Nat in
/-- M5: for every `n ≥ 8` there is a prime `p` with `n < 2p` and `p + 3 ≤ n`. -/
theorem sch_exists_prime_mid (n : ℕ) (hn : 8 ≤ n) : ∃ p, p.Prime ∧ n < 2 * p ∧ p + 3 ≤ n := by
  classical
  by_cases hbig : 4096 ≤ n
  · by_contra hno
    push Not at hno
    set m := n / 2 with hm
    have hm2 : 2048 ≤ m := by omega
    set T : Finset ℕ := ({n - 2, n - 1, n} : Finset ℕ).filter (· ≤ 2 * m)
    have hT : T.card ≤ 3 :=
      (Finset.card_filter_le _ _).trans (Finset.card_le_three)
    have hTle : ∀ x ∈ T, x ≤ 2 * m := fun x hx => (Finset.mem_filter.1 hx).2
    have hprime : ∀ p : ℕ, p.Prime → m < p → p ≤ 2 * m → p ∈ T := by
      intro p hp hmp hp2
      have h1 := hno p hp (by omega)
      refine Finset.mem_filter.2 ⟨?_, hp2⟩
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have hc := sch_centralBinom_le m (by omega) T hT hTle hprime
    have h4 := Nat.four_pow_lt_mul_centralBinom m (by omega)
    have hmain := sch_main_inequality hm2
    have : m * m.centralBinom ≤ m * ((2 * m) ^ sqrt (2 * m) * 4 ^ (2 * m / 3) * (2 * m) ^ 3) :=
      Nat.mul_le_mul_left _ hc
    omega
  · push Not at hbig
    by_cases h1 : n ≤ 9
    · exact ⟨5, by norm_num, by omega, by omega⟩
    by_cases h2 : n ≤ 13
    · exact ⟨7, by norm_num, by omega, by omega⟩
    by_cases h3 : n ≤ 21
    · exact ⟨11, by norm_num, by omega, by omega⟩
    by_cases h4 : n ≤ 37
    · exact ⟨19, by norm_num, by omega, by omega⟩
    by_cases h5 : n ≤ 61
    · exact ⟨31, by norm_num, by omega, by omega⟩
    by_cases h6 : n ≤ 117
    · exact ⟨59, by norm_num, by omega, by omega⟩
    by_cases h7 : n ≤ 225
    · exact ⟨113, by norm_num, by omega, by omega⟩
    by_cases h8 : n ≤ 445
    · exact ⟨223, by norm_num, by omega, by omega⟩
    by_cases h9 : n ≤ 885
    · exact ⟨443, by norm_num, by omega, by omega⟩
    by_cases h10 : n ≤ 1765
    · exact ⟨883, by norm_num, by omega, by omega⟩
    by_cases h11 : n ≤ 3517
    · exact ⟨1759, by norm_num, by omega, by omega⟩
    · exact ⟨3511, by norm_num, by omega, by omega⟩

open Polynomial Finset in
open MulAction Equiv Pointwise in
open Polynomial in
/-- The Galois action, transported to `Fin n` along an enumeration of the roots. -/
noncomputable def schRho (f : ℚ[X]) (n : ℕ) (e : Fin n ≃ f.rootSet f.SplittingField)
    [Fact (f.map (algebraMap ℚ f.SplittingField)).Splits] : f.Gal →* Equiv.Perm (Fin n) :=
  (Equiv.permCongrHom e.symm).toMonoidHom.comp (Gal.galActionHom f f.SplittingField)

open Polynomial Finset in
open MulAction Equiv Pointwise in
open Polynomial in
lemma sch_rho_injective (f : ℚ[X]) (n : ℕ) (e : Fin n ≃ f.rootSet f.SplittingField)
    [Fact (f.map (algebraMap ℚ f.SplittingField)).Splits] : Function.Injective (schRho f n e) :=
  (Equiv.permCongrHom e.symm).injective.comp (Gal.galActionHom_injective f f.SplittingField)

open Polynomial Finset in
open MulAction Equiv Pointwise in
open Polynomial in
lemma sch_rho_apply (f : ℚ[X]) (n : ℕ) (e : Fin n ≃ f.rootSet f.SplittingField)
    [Fact (f.map (algebraMap ℚ f.SplittingField)).Splits] (ϕ : Gal(f.SplittingField/ℚ))
    (i : Fin n) :
    ((e (schRho f n e (Gal.restrict f f.SplittingField ϕ) i) : f.SplittingField)) = ϕ (e i) := by
  change ((e (e.symm (Gal.galActionHom f f.SplittingField
    (Gal.restrict f f.SplittingField ϕ) (e i))) : f.SplittingField)) = ϕ (e i)
  rw [Equiv.apply_symm_apply]
  exact Gal.galActionHom_restrict f f.SplittingField ϕ (e i)

open Polynomial Finset in
open MulAction Equiv Pointwise in
/-- If a subgroup contains `Aₙ` and an odd permutation, it is everything. -/
lemma sch_eq_top_of_alternating_le {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (hA : alternatingGroup (Fin n) ≤ H) {σ : Equiv.Perm (Fin n)} (hσ : σ ∈ H)
    (hsign : Equiv.Perm.sign σ = -1) : H = ⊤ := by
  rw [eq_top_iff]
  intro τ _
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h
  · exact hA (Equiv.Perm.mem_alternatingGroup.mpr h)
  · have : σ⁻¹ * τ ∈ alternatingGroup (Fin n) := by
      rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, hsign, h]; decide
    have := H.mul_mem hσ (hA this)
    rwa [mul_inv_cancel_left] at this

open Polynomial Finset in
open MulAction Equiv Pointwise in
open Polynomial in
lemma sch_map_G (n : ℕ) (L : Type*) [Field L] [Algebra ℚ L] :
    (schG ℚ n).map (algebraMap ℚ L) = schG L n := by
  simp [schG, Polynomial.map_sum]

open Polynomial Finset in
open MulAction Equiv Pointwise in
open Polynomial in
/-- `g_n` splits as the product over an enumeration of the roots of `f`. -/
lemma sch_prod_roots (n : ℕ) (f : ℚ[X]) (hf : schG ℚ n = C (n.factorial : ℚ) * f)
    (hsep : f.Separable) (L : Type*) [Field L] [Algebra ℚ L]
    (hs : (f.map (algebraMap ℚ L)).Splits) (e : Fin n ≃ f.rootSet L) :
    schG L n = ∏ i, (X - C ((e i : L))) := by
  classical
  have hlc : (n.factorial : ℚ) * f.leadingCoeff = 1 := by
    have := (sch_G_monic n).1.leadingCoeff
    rwa [hf, leadingCoeff_mul, leadingCoeff_C] at this
  have hnd : (f.map (algebraMap ℚ L)).roots.Nodup := nodup_roots (hsep.map)
  have hfin : (f.map (algebraMap ℚ L)).roots.toFinset = Finset.univ.image (fun i => (e i : L)) := by
    ext x
    simp only [Multiset.mem_toFinset, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro hx
      have hf0 : f ≠ 0 := hsep.ne_zero
      have hxr : x ∈ f.rootSet L := by
        rw [mem_rootSet]
        refine ⟨hf0, ?_⟩
        have := (mem_roots_map hf0).mp hx
        rwa [aeval_def]
      exact ⟨e.symm ⟨x, hxr⟩, by simp⟩
    · rintro ⟨i, rfl⟩
      have hf0 : f ≠ 0 := hsep.ne_zero
      have h := (mem_rootSet.mp (e i).2).2
      rw [mem_roots_map hf0]
      rwa [aeval_def] at h
  have hprod : ((f.map (algebraMap ℚ L)).roots.map (fun x => X - C x)).prod = ∏ i, (X - C ((e i : L))) := by
    rw [← hnd.dedup, ← Multiset.toFinset_val, ← Finset.prod_eq_multiset_prod, hfin,
      Finset.prod_image (fun i _ j _ h => e.injective (Subtype.ext h))]
  rw [← sch_map_G, hf, Polynomial.map_mul, map_C, hs.eq_prod_roots, hprod, ← mul_assoc, ← C_mul,
    leadingCoeff_map, ← map_mul, hlc, map_one, C_1, one_mul]

open Polynomial Finset in
open MulAction Equiv Pointwise in
open Polynomial in
/-- M8: if the image of the Galois group contains `Aₙ`, the discriminant decides between `Aₙ` and
`Sₙ`. -/
theorem sch_galois_iso (n : ℕ) (hn : 2 ≤ n) (f : ℚ[X]) (hf : schG ℚ n = C (n.factorial : ℚ) * f)
    (hsep : f.Separable) [Fact (f.map (algebraMap ℚ f.SplittingField)).Splits]
    (e : Fin n ≃ f.rootSet f.SplittingField)
    (hA : alternatingGroup (Fin n) ≤ (schRho f n e).range) :
    if n % 4 = 0 then Nonempty (f.Gal ≃* alternatingGroup (Fin n))
    else Nonempty (f.Gal ≃* Equiv.Perm (Fin n)) := by
  classical
  set L := f.SplittingField
  set ρ := schRho f n e
  set H := ρ.range
  have iso0 : f.Gal ≃* H := MonoidHom.ofInjective (sch_rho_injective f n e)
  have hspl : IsSplittingField ℚ L f := by
    convert IsSplittingField.splittingField f
    exact Subsingleton.elim _ _
  haveI : IsGalois ℚ L := IsGalois.of_separable_splitting_field (p := f) hsep
  set v : Fin n → L := fun i => (e i : L)
  have hvinj : Function.Injective v := fun i j h => e.injective (Subtype.ext h)
  have hv : schG L n = ∏ i, (X - C (v i)) :=
    sch_prod_roots n f hf hsep L (Fact.out) e
  set δ := (Matrix.vandermonde v).det
  have hδ0 : δ ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hvinj
  have hδsq : δ ^ 2 = (-1) ^ (∑ k ∈ Finset.range n, k) * ((n.factorial : L)) ^ n := by
    show (Matrix.vandermonde v).det ^ 2 = _
    rw [Matrix.det_vandermonde, sch_delta_sq v hv, sch_P_eq]
  -- the action on `δ`
  have hact : ∀ ϕ : Gal(L/ℚ), ϕ δ =
      (Equiv.Perm.sign (ρ (Gal.restrict f L ϕ)) : ℤ) * δ := by
    intro ϕ
    exact sch_sigma_delta v ϕ _ (fun i => (sch_rho_apply f n e ϕ i).symm)
  have hsurj : ∀ σ ∈ H, ∃ ϕ : Gal(L/ℚ), ρ (Gal.restrict f L ϕ) = σ := by
    rintro σ ⟨g, rfl⟩
    obtain ⟨ϕ, hϕ⟩ := Gal.restrict_surjective f L g
    exact ⟨ϕ, by rw [hϕ]⟩
  have hsign_one : ∀ ϕ : Gal(L/ℚ), ϕ δ = δ → Equiv.Perm.sign (ρ (Gal.restrict f L ϕ)) = 1 := by
    intro ϕ hϕ
    rcases Int.units_eq_one_or (Equiv.Perm.sign (ρ (Gal.restrict f L ϕ))) with h | h
    · exact h
    · exfalso
      have := hact ϕ
      rw [hϕ, h] at this
      push_cast at this
      have h2 : (2 : L) * δ = 0 := by linear_combination this
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact two_ne_zero h3
      · exact hδ0 h3
  split_ifs with h4
  · -- `4 ∣ n`: `δ` is rational, so the image lies in `Aₙ`
    have hP : Even (∑ k ∈ Finset.range n, k) := by
      rw [Nat.even_iff, sch_S_mod]; simp [h4]
    obtain ⟨m, hm⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
    have hsq : δ ^ 2 = (((n.factorial : L)) ^ m) ^ 2 := by
      rw [hδsq, hP.neg_one_pow, one_mul, ← pow_mul, mul_comm m 2, ← hm]
    have hfix : ∀ ϕ : Gal(L/ℚ), ϕ δ = δ := by
      intro ϕ
      have hc : ϕ (((n.factorial : L)) ^ m) = ((n.factorial : L)) ^ m := by
        rw [map_pow, map_natCast]
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
      · rw [h, hc]
      · rw [h, map_neg, hc]
    have hle : H ≤ alternatingGroup (Fin n) := by
      intro σ hσ
      obtain ⟨ϕ, rfl⟩ := hsurj σ hσ
      exact Equiv.Perm.mem_alternatingGroup.mpr (hsign_one ϕ (hfix ϕ))
    exact ⟨iso0.trans (MulEquiv.subgroupCongr (le_antisymm hle hA))⟩
  · -- `4 ∤ n`: `δ` is irrational, so some element is odd
    have hnot : ¬ ∀ ϕ : Gal(L/ℚ), ϕ δ = δ := by
      intro hall
      have hbot : δ ∈ (⊥ : IntermediateField ℚ L) := (IsGalois.mem_bot_iff_fixed δ).mpr hall
      obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp hbot
      have hq2 : algebraMap ℚ L (q ^ 2) =
          algebraMap ℚ L ((-1) ^ (∑ k ∈ Finset.range n, k) * ((n.factorial : ℚ)) ^ n) := by
        rw [map_pow, hq, hδsq, map_mul, map_pow, map_pow, map_neg, map_one, map_natCast]
      have hq2' := (algebraMap ℚ L).injective hq2
      exact h4 ((sch_square_iff n hn).mp ⟨q, by rw [← hq2', sq]⟩)
    push Not at hnot
    obtain ⟨ϕ, hϕ⟩ := hnot
    have hodd : Equiv.Perm.sign (ρ (Gal.restrict f L ϕ)) = -1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign (ρ (Gal.restrict f L ϕ))) with h | h
      · exfalso; apply hϕ; rw [hact ϕ, h]; simp
      · exact h
    have htop := sch_eq_top_of_alternating_le H hA ⟨_, rfl⟩ hodd
    exact ⟨(iso0.trans (MulEquiv.subgroupCongr htop)).trans Subgroup.topEquiv⟩

open Polynomial Finset in
open MulAction Equiv Pointwise in
open Polynomial in
lemma sch_irreducible_of (n : ℕ) (hn : 1 ≤ n) (f : ℚ[X])
    (hf : schG ℚ n = C (n.factorial : ℚ) * f) : Irreducible f := by
  have hg := sch_G_irreducible n hn
  rw [hf, mul_comm] at hg
  exact (associated_mul_unit_right f (C (n.factorial : ℚ))
    (isUnit_C.mpr (IsUnit.mk0 _ (by exact_mod_cast Nat.factorial_ne_zero n)))).irreducible_iff.mpr hg

open Polynomial Finset in
open MulAction Equiv Pointwise in
open Polynomial in
/-- The image of the Galois group is transitive on `Fin n`. -/
lemma sch_rho_pretransitive (n : ℕ) (f : ℚ[X]) (hirr : Irreducible f)
    [Fact (f.map (algebraMap ℚ f.SplittingField)).Splits]
    (e : Fin n ≃ f.rootSet f.SplittingField) :
    MulAction.IsPretransitive (schRho f n e).range (Fin n) := by
  haveI := Gal.galAction_isPretransitive f f.SplittingField hirr
  refine ⟨fun i j => ?_⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq f.Gal (e i) (e j)
  refine ⟨⟨schRho f n e g, g, rfl⟩, ?_⟩
  change e.symm (Gal.galActionHom f f.SplittingField g (e i)) = j
  change e.symm (g • e i) = j
  rw [hg, Equiv.symm_apply_apply]

open Polynomial Finset in
open MulAction Equiv Pointwise in
open Polynomial in
/-- M8 for `n ≥ 8`: the image of the Galois group contains `Aₙ` (Coleman). -/
lemma sch_alt_le_large (n : ℕ) (hn : 8 ≤ n) (f : ℚ[X])
    (hf : schG ℚ n = C (n.factorial : ℚ) * f)
    [Fact (f.map (algebraMap ℚ f.SplittingField)).Splits]
    (e : Fin n ≃ f.rootSet f.SplittingField) :
    alternatingGroup (Fin n) ≤ (schRho f n e).range := by
  classical
  obtain ⟨p, hp, hp2, hp3⟩ := sch_exists_prime_mid n hn
  haveI := Fact.mk hp
  have hirr := sch_irreducible_of n (by omega) f hf
  have hdvd := sch_p_dvd_card_gal p n (by omega) (by omega) hp2 f (n.factorial : ℚ)
    (by exact_mod_cast Nat.factorial_ne_zero n) hf
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvd
  set σ := schRho f n e g
  have hσord : orderOf σ = p := by
    rw [orderOf_injective _ (sch_rho_injective f n e) g, hg]
  have hcard : Fintype.card (Fin n) < 2 * orderOf σ := by rw [Fintype.card_fin, hσord]; exact hp2
  have hcyc : σ.IsCycle := Equiv.Perm.isCycle_of_prime_order' (hσord ▸ hp) hcard
  have hsupp : σ.support.card = p := by rw [← hcyc.orderOf, hσord]
  have hσH : σ ∈ (schRho f n e).range := ⟨g, rfl⟩
  haveI := sch_rho_pretransitive n f hirr e
  have hprim := sch_isPreprimitive_of_long_cycle (schRho f n e).range hcyc hσH
    (hsupp ▸ hp) (by rw [Fintype.card_fin, hsupp]; exact hp2)
  exact sch_alternatingGroup_le_of_isPreprimitive_of_isCycle_mem hprim hp
    (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hp3) hcyc hsupp hσH


open Polynomial Finset in
open MulAction Equiv Pointwise in
open Polynomial in
lemma sch_G_eq_truncatedExp (n : ℕ) :
    schG ℚ n = C (n.factorial : ℚ) * SchurTruncatedExponential.truncatedExp n := by
  unfold schG SchurTruncatedExponential.truncatedExp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  have hdvd : j.factorial ∣ n.factorial := Nat.factorial_dvd_factorial (by omega)
  rw [Nat.cast_div hdvd (by exact_mod_cast Nat.factorial_ne_zero j), smul_eq_C_mul, ← mul_assoc,
    ← C_mul]
  congr 2
  field_simp

open Polynomial Finset in
open MulAction Equiv Pointwise in
open Polynomial in
/-- Schur's theorem for `n ≥ 8`. -/
theorem sch_schur_large (n : ℕ) (hn : 8 ≤ n) :
    if n % 4 = 0 then
      Nonempty ((SchurTruncatedExponential.truncatedExp n).Gal ≃* alternatingGroup (Fin n))
    else Nonempty ((SchurTruncatedExponential.truncatedExp n).Gal ≃* Equiv.Perm (Fin n)) := by
  classical
  set f := SchurTruncatedExponential.truncatedExp n
  have hf := sch_G_eq_truncatedExp n
  have hirr := sch_irreducible_of n (by omega) f hf
  have hsep : f.Separable := hirr.separable
  haveI : Fact (f.map (algebraMap ℚ f.SplittingField)).Splits := ⟨SplittingField.splits f⟩
  have hdeg : f.natDegree = n := by
    have h := (sch_G_monic n).2
    rw [hf, natDegree_C_mul (by exact_mod_cast Nat.factorial_ne_zero n)] at h
    exact h
  have hcard : Fintype.card (f.rootSet f.SplittingField) = n := by
    exact (card_rootSet_eq_natDegree hsep (SplittingField.splits f)).trans hdeg
  let e : Fin n ≃ f.rootSet f.SplittingField := (Fintype.equivFinOfCardEq hcard).symm
  exact sch_galois_iso n (by omega) f hf hsep e (sch_alt_le_large n hn f hf e)

open Polynomial Finset in
open MulAction Equiv Pointwise in
open Polynomial in
/-- In a field of characteristic `p`, the solutions of `y ^ p = y` are the images of `0, …, p-1`. -/
lemma sch_frob_fixed (p : ℕ) [hp : Fact p.Prime] (κ : Type*) [Field κ] [CharP κ p] (y : κ)
    (hy : y ^ p = y) : ∃ t ∈ Finset.range p, y = (t : κ) := by
  classical
  set P : κ[X] := X ^ p - X
  have hP0 : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero κ hp.out.one_lt
  have hdeg : P.natDegree = p := FiniteField.X_pow_card_sub_X_natDegree_eq κ hp.out.one_lt
  set Z := (Finset.range p).image (fun t : ℕ => (t : κ))
  have hZcard : Z.card = p := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb hab
    exact CharP.natCast_injOn_Iio κ p (by simpa using ha) (by simpa using hb) hab
  have hZsub : Z ⊆ P.roots.toFinset := by
    intro z hz
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hz
    rw [Multiset.mem_toFinset, mem_roots hP0, IsRoot]
    simp only [P, eval_sub, eval_pow, eval_X]
    rw [← frobenius_def, map_natCast, sub_self]
  have hle : P.roots.toFinset.card ≤ Z.card := by
    rw [hZcard, ← hdeg]
    exact (Multiset.toFinset_card_le _).trans (card_roots' P)
  have hZeq := Finset.eq_of_subset_of_card_le hZsub hle
  have hyroot : y ∈ P.roots.toFinset := by
    rw [Multiset.mem_toFinset, mem_roots hP0, IsRoot]
    simp only [P, eval_sub, eval_pow, eval_X, hy, sub_self]
  rw [← hZeq] at hyroot
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hyroot
  exact ⟨t, ht, rfl⟩

open Polynomial Finset in
open MulAction Equiv Pointwise in
open Polynomial in
/-- M7 (abstract): a permutation `τ` of the roots that acts as Frobenius on the residues has
exactly three moved points, when `g_n ≡ c · ∏_{t ∈ T} (X - t) (mod p)` with `c` having no root
mod `p` and `|T| = n - 3`. -/
lemma sch_frob_support (n p : ℕ) [hp : Fact p.Prime] (hpn : n < p) (κ : Type*) [Field κ]
    [CharP κ p] (y : Fin n → κ) (hy : schG κ n = ∏ i, (X - C (y i)))
    (τ : Equiv.Perm (Fin n)) (hτ : ∀ i, y (τ i) = y i ^ p)
    (c r : ℤ[X]) (T : Finset ℤ)
    (hid : schG ℤ n = c * ∏ t ∈ T, (X - C t) + C (p : ℤ) * r)
    (hT : T.card + 3 = n) (hTinj : ∀ t ∈ T, ∀ t' ∈ T, (p : ℤ) ∣ t - t' → t = t')
    (hc : ∀ t ∈ Finset.range p, ¬ (p : ℤ) ∣ c.eval (t : ℤ)) :
    τ.support.card = 3 := by
  classical
  have hmapG : (schG ℤ n).map (Int.castRingHom κ) = schG κ n := by
    unfold schG
    rw [Polynomial.map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Polynomial.map_mul, map_C, Polynomial.map_pow, map_X, eq_intCast, Int.cast_natCast]
  -- factorization over `κ`
  have hfac : schG κ n = c.map (Int.castRingHom κ) * ∏ t ∈ T, (X - C ((t : ℤ) : κ)) := by
    rw [← hmapG, hid, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
      Polynomial.map_prod]
    have hp0 : (C (p : ℤ)).map (Int.castRingHom κ) = 0 := by
      rw [map_C]; simp [CharP.cast_eq_zero κ p]
    rw [hp0, zero_mul, add_zero]
    congr 1
    apply Finset.prod_congr rfl
    intro t _
    simp
  have hroot : ∀ i, eval (y i) (schG κ n) = 0 := by
    intro i
    rw [hy, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  -- `n! ≠ 0` in `κ`
  have hfact : (n.factorial : κ) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff κ p n.factorial).mp h
    exact absurd ((hp.out.dvd_factorial).mp this) (by omega)
  -- the residues are pairwise distinct
  have hyinj : Function.Injective y := by
    intro i j hij
    by_contra hne
    have h1 := sch_eval_derivative_prod y i
    rw [← hy, sch_derivative_G, eval_sub, hroot i, eval_pow, eval_X, zero_sub] at h1
    have h2 : ∏ k ∈ Finset.univ.erase i, (y i - y k) = 0 :=
      Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨fun h => hne h.symm, Finset.mem_univ j⟩)
        (by rw [hij, sub_self])
    rw [h2] at h1
    have hyi : y i = 0 := by
      have : y i ^ n = 0 := by linear_combination -h1
      exact pow_eq_zero_iff (by omega : n ≠ 0) |>.mp this
    have h3 := hroot i
    rw [hyi, sch_eval_zero_G] at h3
    exact hfact h3
  -- fixed points of `τ`
  have hfix_iff : ∀ i, τ i = i ↔ y i ^ p = y i := by
    intro i
    constructor
    · intro h; rw [← hτ i, h]
    · intro h; exact hyinj (by rw [hτ i, h])
  have hcast_fix : ∀ t : ℤ, ((t : κ)) ^ p = (t : κ) := by
    intro t; rw [← frobenius_def, map_intCast]
  have hmoved : ∀ i, (∀ t ∈ T, y i ≠ ((t : ℤ) : κ)) → τ i ≠ i := by
    intro i hi hτi
    have hpow := (hfix_iff i).mp hτi
    obtain ⟨t, ht, hyt⟩ := sch_frob_fixed p κ (y i) hpow
    have h0 := hroot i
    rw [hfac, eval_mul, eval_prod] at h0
    rcases mul_eq_zero.mp h0 with h1 | h1
    · rw [hyt, show ((t : ℕ) : κ) = (((t : ℕ) : ℤ) : κ) by push_cast; rfl, eval_intCast_map,
        eq_intCast, CharP.intCast_eq_zero_iff κ p] at h1
      exact hc t ht h1
    · obtain ⟨t', ht', h2⟩ := Finset.prod_eq_zero_iff.mp h1
      simp only [eval_sub, eval_X, eval_C] at h2
      exact hi t' ht' (sub_eq_zero.mp h2)
  have hfixed : ∀ i, (∃ t ∈ T, y i = ((t : ℤ) : κ)) → τ i = i := by
    rintro i ⟨t, -, hyt⟩
    rw [hfix_iff, hyt, hcast_fix]
  -- the fixed set is in bijection with `T`
  have hTroot : ∀ t ∈ T, ∃ i, y i = ((t : ℤ) : κ) := by
    intro t ht
    have h0 : eval ((t : ℤ) : κ) (schG κ n) = 0 := by
      rw [hfac, eval_mul, eval_prod]
      exact mul_eq_zero_of_right _ (Finset.prod_eq_zero ht (by simp))
    rw [hy, eval_prod] at h0
    obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp h0
    simp only [eval_sub, eval_X, eval_C] at hi
    exact ⟨i, (sub_eq_zero.mp hi).symm⟩
  have hTcast_inj : ∀ t ∈ T, ∀ t' ∈ T, ((t : ℤ) : κ) = ((t' : ℤ) : κ) → t = t' := by
    intro t ht t' ht' h
    apply hTinj t ht t' ht'
    rw [← CharP.intCast_eq_zero_iff κ p]; push_cast; rw [h, sub_self]
  set Fx : Finset (Fin n) := Finset.univ.filter (fun i => ∃ t ∈ T, y i = ((t : ℤ) : κ))
  have hFx : Fx.card = T.card := by
    choose idx hidx using hTroot
    symm
    apply Finset.card_bij (fun t ht => idx t ht)
    · intro t ht
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, ht, hidx t ht⟩
    · intro t ht t' ht' h
      apply hTcast_inj t ht t' ht'
      rw [← hidx t ht, ← hidx t' ht', h]
    · intro i hi
      obtain ⟨-, t, ht, hyt⟩ := Finset.mem_filter.mp hi
      exact ⟨t, ht, hyinj (by rw [hidx t ht, hyt])⟩
  have hsupp : τ.support = Finset.univ \ Fx := by
    ext i
    simp only [Equiv.Perm.mem_support, Finset.mem_sdiff, Finset.mem_univ, true_and, Fx,
      Finset.mem_filter, not_exists, not_and]
    constructor
    · intro hne t ht hyt
      exact hne (hfixed i ⟨t, ht, hyt⟩)
    · intro h
      exact hmoved i h
  rw [hsupp, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    Fintype.card_fin, hFx]
  omega

open Polynomial Finset in
open MulAction Equiv Pointwise in
open Polynomial in
lemma sch_map_G_gen {A B : Type*} [CommRing A] [CommRing B] (ψ₀ : A →+* B) (n : ℕ) :
    (schG A n).map ψ₀ = schG B n := by
  unfold schG
  rw [Polynomial.map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Polynomial.map_mul, map_C, Polynomial.map_pow, map_X, map_natCast]

open Polynomial Finset in
open MulAction Equiv Pointwise in
open Polynomial in
lemma sch_G_monic_int (n : ℕ) : (schG ℤ n).Monic := by
  have h : schG ℤ n = X ^ n + ∑ j ∈ Finset.range n,
      C ((n.factorial / j.factorial : ℕ) : ℤ) * X ^ j := by
    unfold schG
    rw [Finset.sum_range_succ, Nat.div_self (Nat.factorial_pos n)]
    simp [add_comm]
  rw [h]
  apply monic_X_pow_add
  refine lt_of_le_of_lt (degree_sum_le _ _) ?_
  refine (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).mpr ?_
  intro j hj
  rw [Finset.mem_range] at hj
  exact lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) (WithBot.coe_lt_coe.mpr hj)

open Polynomial Finset in
open MulAction Equiv Pointwise in
open Polynomial NumberField in
/-- M7: a Frobenius element at a prime `p > n` with `g_n ≡ c · ∏_{t ∈ T} (X - t) (mod p)` gives a
3-cycle in the image of the Galois group. -/
lemma sch_three_cycle_mem (n p : ℕ) [hp : Fact p.Prime] (hn : 1 ≤ n) (hpn : n < p) (f : ℚ[X])
    (hf : schG ℚ n = C (n.factorial : ℚ) * f)
    [Fact (f.map (algebraMap ℚ f.SplittingField)).Splits]
    (e : Fin n ≃ f.rootSet f.SplittingField) (c r : ℤ[X]) (T : Finset ℤ)
    (hid : schG ℤ n = c * ∏ t ∈ T, (X - C t) + C (p : ℤ) * r)
    (hT : T.card + 3 = n) (hTinj : ∀ t ∈ T, ∀ t' ∈ T, (p : ℤ) ∣ t - t' → t = t')
    (hc : ∀ t ∈ Finset.range p, ¬ (p : ℤ) ∣ c.eval (t : ℤ)) :
    ∃ σ ∈ (schRho f n e).range, σ.IsThreeCycle := by
  classical
  have hirr := sch_irreducible_of n hn f hf
  have hsep : f.Separable := hirr.separable
  set L := f.SplittingField
  letI : NumberField L := NumberField.of_module_finite ℚ L
  have hspl : IsSplittingField ℚ L f := by
    convert IsSplittingField.splittingField f
    exact Subsingleton.elim _ _
  haveI : IsGalois ℚ L := IsGalois.of_separable_splitting_field (p := f) hsep
  -- a prime of `𝓞 L` above `p` and its Frobenius element
  set P : Ideal ℤ := Ideal.span {(p : ℤ)}
  haveI hPmax : P.IsMaximal := by
    apply Ideal.IsPrime.isMaximal inferInstance
    simp [P, hp.out.ne_zero]
  obtain ⟨⟨Q, hQ⟩⟩ := Ideal.nonempty_primesOver (S := 𝓞 L) P
  haveI := hQ.1
  haveI := hQ.2
  haveI hQmax : Q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal Q P
  letI : Field (𝓞 L ⧸ Q) := Ideal.Quotient.field Q
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ Gal(L/ℚ) Q
  have hN : Nat.card (ℤ ⧸ Ideal.under ℤ Q) = p := by
    rw [← Ideal.over_def Q P, Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv,
      Nat.card_zmod]
  have hpQ : ((p : ℕ) : 𝓞 L) ∈ Q := by
    have h1 : (p : ℤ) ∈ P := Ideal.subset_span rfl
    rw [Ideal.over_def Q P, Ideal.mem_comap] at h1
    simpa using h1
  haveI : CharP (𝓞 L ⧸ Q) p := by
    rw [CharP.charP_iff_prime_eq_zero hp.out]
    have := Ideal.Quotient.eq_zero_iff_mem.mpr hpQ
    simpa using this
  -- the roots in `𝓞 L`
  have hv : schG L n = ∏ i, (X - C ((e i : L))) :=
    sch_prod_roots n f hf hsep L (Fact.out) e
  have hint : ∀ i, IsIntegral ℤ ((e i : L)) := by
    intro i
    refine ⟨schG ℤ n, sch_G_monic_int n, ?_⟩
    rw [← eval_map, sch_map_G_gen, hv, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  set vO : Fin n → 𝓞 L := fun i => ⟨e i, hint i⟩
  have hinj : Function.Injective (algebraMap (𝓞 L) L) := FaithfulSMul.algebraMap_injective _ _
  have hvO : schG (𝓞 L) n = ∏ i, (X - C (vO i)) := by
    apply Polynomial.map_injective (algebraMap (𝓞 L) L) hinj
    rw [sch_map_G_gen, hv, Polynomial.map_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [Polynomial.map_sub, map_X, map_C]
    rfl
  set y : Fin n → 𝓞 L ⧸ Q := fun i => Ideal.Quotient.mk Q (vO i)
  have hy : schG (𝓞 L ⧸ Q) n = ∏ i, (X - C (y i)) := by
    rw [← sch_map_G_gen (Ideal.Quotient.mk Q), hvO, Polynomial.map_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [Polynomial.map_sub, map_X, map_C]
  set τ := schRho f n e (Gal.restrict f L σ)
  have hτ : ∀ i, y (τ i) = y i ^ p := by
    intro i
    have h1 : vO (τ i) = σ • vO i := by
      apply hinj
      exact sch_rho_apply f n e σ i
    have h2 := hσ (vO i)
    rw [hN, MulSemiringAction.toAlgHom_apply] at h2
    simp only [y]
    rw [h1, ← map_pow]
    exact Ideal.Quotient.eq.mpr h2
  have hsupp := sch_frob_support n p hpn (𝓞 L ⧸ Q) y hy τ hτ c r T hid hT hTinj hc
  exact ⟨τ, ⟨_, rfl⟩, card_support_eq_three_iff.mp hsupp⟩

open Polynomial Finset in
open MulAction Equiv Pointwise in
open Polynomial in
/-- A cycle of prime length `p` in the image, for `p ≤ n < 2p`, and primitivity of the image. -/
lemma sch_cycle_and_primitive (n p : ℕ) [hp : Fact p.Prime] (hn : 1 ≤ n) (hpn : p ≤ n)
    (hnp : n < 2 * p) (f : ℚ[X]) (hf : schG ℚ n = C (n.factorial : ℚ) * f)
    [Fact (f.map (algebraMap ℚ f.SplittingField)).Splits]
    (e : Fin n ≃ f.rootSet f.SplittingField) :
    (∃ σ ∈ (schRho f n e).range, σ.IsCycle ∧ σ.support.card = p) ∧
      MulAction.IsPreprimitive (schRho f n e).range (Fin n) := by
  classical
  have hirr := sch_irreducible_of n hn f hf
  have hdvd := sch_p_dvd_card_gal p n hn hpn hnp f (n.factorial : ℚ)
    (by exact_mod_cast Nat.factorial_ne_zero n) hf
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvd
  set σ := schRho f n e g
  have hσord : orderOf σ = p := by
    rw [orderOf_injective _ (sch_rho_injective f n e) g, hg]
  have hcard : Fintype.card (Fin n) < 2 * orderOf σ := by rw [Fintype.card_fin, hσord]; exact hnp
  have hcyc : σ.IsCycle := Equiv.Perm.isCycle_of_prime_order' (hσord ▸ hp.out) hcard
  have hsupp : σ.support.card = p := by rw [← hcyc.orderOf, hσord]
  have hσH : σ ∈ (schRho f n e).range := ⟨g, rfl⟩
  haveI := sch_rho_pretransitive n f hirr e
  exact ⟨⟨σ, hσH, hcyc, hsupp⟩, sch_isPreprimitive_of_long_cycle (schRho f n e).range hcyc hσH
    (hsupp ▸ hp.out) (by rw [Fintype.card_fin, hsupp]; exact hnp)⟩

open Polynomial Finset in
open MulAction Equiv Pointwise in
lemma sch_c7_no_root : ∀ t ∈ Finset.range 191,
    ¬ (191 : ℤ) ∣ ((t : ℤ) ^ 3 + 183 * (t : ℤ) ^ 2 + 43 * (t : ℤ) + 44) := by
  decide +kernel

open Polynomial Finset in
open MulAction Equiv Pointwise in
open Polynomial in
/-- M7: the image of the Galois group contains `Aₙ` for `2 ≤ n ≤ 7`. -/
lemma sch_alt_le_small (n : ℕ) (hn : 2 ≤ n) (hn7 : n ≤ 7) (f : ℚ[X])
    (hf : schG ℚ n = C (n.factorial : ℚ) * f)
    [Fact (f.map (algebraMap ℚ f.SplittingField)).Splits]
    (e : Fin n ≃ f.rootSet f.SplittingField) :
    alternatingGroup (Fin n) ≤ (schRho f n e).range := by
  classical
  by_cases h2 : n = 2
  · subst h2
    intro σ hσ
    have : ∀ τ : Equiv.Perm (Fin 2), Equiv.Perm.sign τ = 1 → τ = 1 := by decide
    rw [this σ (Equiv.Perm.mem_alternatingGroup.mp hσ)]
    exact one_mem _
  by_cases h5 : n ≤ 5
  · -- a 3-cycle from the prime 3
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨⟨σ, hσH, hcyc, hsupp⟩, hprim⟩ :=
      sch_cycle_and_primitive n 3 (by omega) (by omega) (by omega) f hf e
    exact Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim
      (card_support_eq_three_iff.mp hsupp) hσH
  by_cases h6 : n = 6
  · subst h6
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    haveI : Fact (Nat.Prime 41) := ⟨by norm_num⟩
    obtain ⟨-, hprim⟩ := sch_cycle_and_primitive 6 5 (by omega) (by omega) (by omega) f hf e
    obtain ⟨σ, hσH, h3⟩ := sch_three_cycle_mem 6 41 (by omega) (by omega) f hf e
      (X ^ 3 + 5 * X ^ 2 + 6 * X + 34)
      (2 * X ^ 5 - 42 * X ^ 4 + 208 * X ^ 3 + 2043 * X ^ 2 + 972 * X + 15534)
      ({21, 27, 33} : Finset ℤ)
      (by
        simp only [schG, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial,
          Finset.prod_insert, Finset.prod_singleton, Finset.mem_insert, Finset.mem_singleton]
        norm_num
        ring)
      (by decide)
      (by decide)
      (by
        intro t ht
        simp only [eval_add, eval_mul, eval_pow, eval_X, eval_ofNat]
        revert t
        decide)
    exact Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim h3 hσH
  · have h7 : n = 7 := by omega
    subst h7
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    haveI : Fact (Nat.Prime 191) := ⟨by norm_num⟩
    obtain ⟨-, hprim⟩ := sch_cycle_and_primitive 7 7 (by omega) (by omega) (by omega) f hf e
    obtain ⟨σ, hσH, h3⟩ := sch_three_cycle_mem 7 191 (by omega) (by omega) f hf e
      (X ^ 3 + 183 * X ^ 2 + 43 * X + 44)
      (X ^ 6 + 140 * X ^ 5 - 32195 * X ^ 4 + 1139588 * X ^ 3 - 5493028 * X ^ 2 - 1069920 * X
        - 1385136)
      ({6, 39, 146, 176} : Finset ℤ)
      (by
        simp only [schG, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial,
          Finset.prod_insert, Finset.prod_singleton, Finset.mem_insert, Finset.mem_singleton]
        norm_num
        ring)
      (by decide)
      (by decide)
      (by
        intro t ht
        simp only [eval_add, eval_mul, eval_pow, eval_X, eval_ofNat]
        exact sch_c7_no_root t ht)
    exact Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim h3 hσH

open Polynomial Finset in
open MulAction Equiv Pointwise in
open Polynomial in
/-- Schur's theorem for the truncated exponential polynomials (all `n ≥ 2`). -/
theorem sch_schur (n : ℕ) (hn : 2 ≤ n) :
    if n % 4 = 0 then
      Nonempty ((SchurTruncatedExponential.truncatedExp n).Gal ≃* alternatingGroup (Fin n))
    else Nonempty ((SchurTruncatedExponential.truncatedExp n).Gal ≃* Equiv.Perm (Fin n)) := by
  classical
  by_cases h8 : 8 ≤ n
  · exact sch_schur_large n h8
  set f := SchurTruncatedExponential.truncatedExp n
  have hf := sch_G_eq_truncatedExp n
  have hirr := sch_irreducible_of n (by omega) f hf
  have hsep : f.Separable := hirr.separable
  haveI : Fact (f.map (algebraMap ℚ f.SplittingField)).Splits := ⟨SplittingField.splits f⟩
  have hdeg : f.natDegree = n := by
    have h := (sch_G_monic n).2
    rw [hf, natDegree_C_mul (by exact_mod_cast Nat.factorial_ne_zero n)] at h
    exact h
  have hcard : Fintype.card (f.rootSet f.SplittingField) = n :=
    (card_rootSet_eq_natDegree hsep (SplittingField.splits f)).trans hdeg
  let e : Fin n ≃ f.rootSet f.SplittingField := (Fintype.equivFinOfCardEq hcard).symm
  exact sch_galois_iso n hn f hf hsep e (sch_alt_le_small n hn (by omega) f hf e)

/--
**Schur's Theorem (1924):**
Let `f_n(x) = ∑_{j=0}^n x^j/j!` be the `n`-th truncated
exponential polynomial over `ℚ`. Then for `n ≥ 2`:

- If `n ≡ 0 (mod 4)`, the Galois group of `f_n` is isomorphic to the alternating group `A_n`
- If `n ≢ 0 (mod 4)`, the Galois group of `f_n` is isomorphic to the symmetric group `S_n`
-/
@[category research solved, AMS 12]
theorem schur_truncatedExp_galoisGroup_equiv (n : ℕ) (hn : n ≥ 2) :
  letI f := truncatedExp n
  if n % 4 = 0 then
    -- Galois group is alternating group A_n
    Nonempty (f.Gal ≃* alternatingGroup (Fin n))
  else
    -- Galois group is symmetric group S_n
    Nonempty (f.Gal ≃* Equiv.Perm (Fin n)) := by
  exact sch_schur n hn

end SchurTruncatedExponential
