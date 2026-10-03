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
# Erdős Problem 263

*Reference:* [erdosproblems.com/263](https://www.erdosproblems.com/263)
-/

@[expose] public section

open Filter
open scoped Topology

namespace Erdos263

/--
We call a **strictly increasing** sequence $a_n$ of positive integers an
_irrationality sequence_ if for any sequence $b_n$ of positive integers with
$\frac{a_n}{b_n} \to 1$ as $n \to \infty$,
the sum $\sum \frac{1}{b_n}$ converges to an irrational number.

Note: erdosproblems.com/263 was corrected on 2026-04-02 to require the sequence
to be increasing; the pre-correction statement (no monotonicity hypothesis) had a
counterexample to Q2 that is not increasing (see `erdos_263.parts.ii` below).

Note: This is one of many possible notions of "irrationality sequences". See
FormalConjectures/ErdosProblems/264.lean for another possible definition.
-/
def IsIrrationalitySequence (a : ℕ → ℕ) : Prop :=
  (∀ n : ℕ, a n > 0) ∧
    StrictMono a ∧
    (∀ b : ℕ → ℕ, (∀ n : ℕ, b n > 0) ∧
      atTop.Tendsto (fun n : ℕ => (a n : ℝ) / (b n : ℝ)) (𝓝 1) →
      Irrational (∑' n, 1 / (b n : ℝ)))

/-- The nondecreasing version of `IsIrrationalitySequence`, as used by Koizumi [Ko25]: the sequence
is positive and nondecreasing, and every positive sequence asymptotic to it has irrational
reciprocal sum. -/
def IsWeakIrrationalitySequence (a : ℕ → ℕ) : Prop :=
  (∀ n : ℕ, a n > 0) ∧
    Monotone a ∧
    (∀ b : ℕ → ℕ, (∀ n : ℕ, b n > 0) ∧
      atTop.Tendsto (fun n : ℕ => (a n : ℝ) / (b n : ℝ)) (𝓝 1) →
      Irrational (∑' n, 1 / (b n : ℝ)))

/--
Is $a_n = 2^{2^n}$ an irrationality sequence in the above sense?
-/
@[category research open, AMS 11]
theorem erdos_263.parts.i : answer(sorry) ↔ IsIrrationalitySequence (fun n : ℕ => 2 ^ 2 ^ n) := by
  sorry

/--
Must every irrationality sequence $a_n$ in the above sense
satisfy $a_n^{1/n} \to \infty$ as $n \to \infty$?

Note: this was answered **false** for the *pre-correction* statement, which did not
require monotonicity — the counterexample sequence is not increasing. The problem
was corrected on erdosproblems.com on 2026-04-02 to require increasing sequences;
for the corrected statement this question is **open**. The earlier formal proof
(for the pre-correction definition) is preserved at
https://github.com/google-deepmind/formal-conjectures/blob/c8cf651906abe91051cf835d4232ad5648412113/FormalConjectures/ErdosProblems/263.lean#L298
-/
@[category research open, AMS 11]
theorem erdos_263.parts.ii : answer(sorry) ↔
    ∀ a : ℕ → ℕ,
      IsIrrationalitySequence a →
        atTop.Tendsto (fun n : ℕ => (a n : ℝ) ^ (1 / (n : ℝ))) atTop := by
  sorry

/--
A folklore result states that any $a_n$ satisfying $\lim_{n \to \infty} a_n^{\frac{1}{2^n}} = \infty$
has $\sum \frac{1}{a_n}$ converging to an irrational number.
-/
@[category research solved, AMS 11]
theorem erdos_263.variants.folklore (a : ℕ -> ℕ)
    (ha : atTop.Tendsto (fun n : ℕ => (a n : ℝ) ^ (1 / (2 ^ n : ℝ))) atTop) :
    Irrational <| ∑' n, (1 : ℝ) / (a n : ℝ) := by
  sorry

/--
Kovač and Tao [KoTa24] proved that any strictly increasing sequence $a_n$ such that
$\sum \frac{1}{a_n}$ converges and $\lim \frac{a_{n+1}}{a_n^2} = 0$ is not
an irrationality sequence in the above sense.

[KoTa24] Kovač, V. and Tao T., On several irrationality problems for Ahmes series.
         arXiv:2406.17593 (2024).
-/
@[category research solved, AMS 11]
theorem erdos_263.variants.sub_doubly_exponential (a: ℕ -> ℕ)
    (ha' : StrictMono a)
    (ha'' : Summable (fun n : ℕ => 1 / (a n : ℝ)))
    (ha''' : atTop.Tendsto (fun n : ℕ => (a (n + 1) : ℝ) / a n ^ 2) (𝓝 0)) :
    ¬ IsIrrationalitySequence a := by
  sorry

/--
On the other hand, if there exists some $\varepsilon > 0$ such that $a_n$ satisfies
$\liminf \frac{a_{n+1}}{a_n^{2+\varepsilon}} > 0$, then $a_n$ is an irrationality sequence
by the above folklore result `erdos_263.variants.folklore`.
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://github.com/arex1337/erdos-263-lean/blob/95de79a5cd49050df80e95be6cfc161580830799/Erdos263/Folklore.lean#L700"]
theorem erdos_263.variants.super_doubly_exponential (a: ℕ -> ℕ)
    (ha : ∀ n : ℕ, a n > 0)
    (ha' : StrictMono a)
    (ha'' : ∃ ε : ℝ, ε > 0 ∧
      Filter.atTop.liminf (fun n : ℕ => (a (n + 1) : ℝ) / a n ^ (2 + ε)) > 0) :
    IsIrrationalitySequence a := by
  sorry

open Finset in
lemma e263_two_mul (J : ℕ) : 2 * J ≤ 2 ^ J := by
  induction J with
  | zero => simp
  | succ J ih =>
    rcases Nat.eq_zero_or_pos J with rfl | hJ
    · simp
    · have : 2 ≤ 2 ^ J := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ J := Nat.pow_le_pow_right (by norm_num) hJ
      rw [pow_succ]; omega

open Finset in
lemma e263_sq_le (J : ℕ) : J * (J - 1) + 1 ≤ 2 ^ J := by
  induction J with
  | zero => simp
  | succ J ih =>
    have h1 := e263_two_mul J
    have : (J + 1) * (J + 1 - 1) = J * (J - 1) + 2 * J := by
      rcases Nat.eq_zero_or_pos J with rfl | hJ
      · simp
      obtain ⟨i, rfl⟩ : ∃ i, J = i + 1 := ⟨J - 1, by omega⟩
      simp only [Nat.add_sub_cancel]; ring
    rw [this, pow_succ]; omega

open Finset in
lemma e263_numeric (M P J : ℕ) (hM : 1 ≤ M) (hP : 1 ≤ P) :
    2 * M * (M ^ J * 2 ^ (J * (J - 1)) * P ^ (J + 1)) ≤ (2 * M * P) ^ 2 ^ J := by
  have h1 : J + 1 ≤ 2 ^ J := Nat.lt_two_pow_self
  have h2 := e263_sq_le J
  have hPp : P ^ (J + 1) ≤ P ^ 2 ^ J := Nat.pow_le_pow_right hP h1
  have hMp : M ^ (J + 1) ≤ M ^ 2 ^ J := Nat.pow_le_pow_right hM h1
  have h2p : 2 ^ (J * (J - 1) + 1) ≤ 2 ^ 2 ^ J := Nat.pow_le_pow_right (by norm_num) h2
  calc 2 * M * (M ^ J * 2 ^ (J * (J - 1)) * P ^ (J + 1))
      = 2 ^ (J * (J - 1) + 1) * M ^ (J + 1) * P ^ (J + 1) := by ring
    _ ≤ 2 ^ 2 ^ J * M ^ 2 ^ J * P ^ 2 ^ J := by gcongr
    _ = (2 * M * P) ^ 2 ^ J := by rw [mul_pow, mul_pow]

open Finset in
/-- Step of the doubling argument. -/
lemma e263_step (b : ℕ → ℕ) (hmono : Monotone b) (hpos : ∀ k, 1 ≤ b k) (M R N j : ℕ) (hM : 1 ≤ M)
    (hgood : 2 * M * ∏ k ∈ range N, b k ≤ R ^ 2 ^ N)
    (hj : b (j + N) < M * 2 ^ j * ∏ k ∈ range N, b k) :
    2 * M * ∏ k ∈ range (N + (j + 1)), b k ≤ R ^ 2 ^ (N + (j + 1)) := by
  set P := ∏ k ∈ range N, b k with hPdef
  have hP : 1 ≤ P := Finset.one_le_prod' (fun k _ => hpos k)
  have hprod : ∏ k ∈ range (N + (j + 1)), b k = P * ∏ i ∈ range (j + 1), b (N + i) :=
    Finset.prod_range_add _ _ _
  have hle : ∏ i ∈ range (j + 1), b (N + i) ≤ (M * 2 ^ j * P) ^ (j + 1) := by
    have := Finset.prod_le_pow_card (range (j + 1)) (fun i => b (N + i)) (M * 2 ^ j * P) (by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have : b (N + i) ≤ b (j + N) := hmono (by omega)
      omega)
    simpa using this
  have hJ : P * (M * 2 ^ j * P) ^ (j + 1) = M ^ (j + 1) * 2 ^ ((j + 1) * (j + 1 - 1)) * P ^ (j + 1 + 1) := by
    simp only [Nat.add_sub_cancel]; rw [mul_pow, mul_pow, ← pow_mul]; ring
  have hMP : 2 * M * P ≤ R ^ 2 ^ N := hgood
  calc 2 * M * ∏ k ∈ range (N + (j + 1)), b k
      ≤ 2 * M * (P * (M * 2 ^ j * P) ^ (j + 1)) := by rw [hprod]; gcongr
    _ = 2 * M * (M ^ (j + 1) * 2 ^ ((j + 1) * (j + 1 - 1)) * P ^ (j + 1 + 1)) := by rw [hJ]
    _ ≤ (2 * M * P) ^ 2 ^ (j + 1) := e263_numeric M P (j + 1) hM hP
    _ ≤ (R ^ 2 ^ N) ^ 2 ^ (j + 1) := Nat.pow_le_pow_left hMP _
    _ = R ^ 2 ^ (N + (j + 1)) := by rw [← pow_mul, ← pow_add]

open Finset in
/-- Key: some cut `N` has every later term at least `M 2^n P_N`. -/
lemma e263_key (b : ℕ → ℕ) (hmono : Monotone b) (hpos : ∀ k, 1 ≤ b k)
    (hG : ∀ R : ℕ, ∀ᶠ n in atTop, R ^ 2 ^ n < b n) (M : ℕ) (hM : 1 ≤ M) :
    ∃ N, ∀ n, M * 2 ^ n * ∏ k ∈ range N, b k ≤ b (n + N) := by
  by_contra hcon
  push_neg at hcon
  set R := 2 * M with hR
  have hgood : ∀ k, ∃ N, k ≤ N ∧ 2 * M * ∏ i ∈ range N, b i ≤ R ^ 2 ^ N := by
    intro k
    induction k with
    | zero => exact ⟨0, le_rfl, by simp [hR]⟩
    | succ k ih =>
      obtain ⟨N, hkN, hN⟩ := ih
      obtain ⟨j, hj⟩ := hcon N
      exact ⟨N + (j + 1), by omega, e263_step b hmono hpos M R N j hM hN hj⟩
  obtain ⟨K, hK⟩ := (hG (R ^ 2)).exists_forall_of_atTop
  obtain ⟨N, hKN, hN⟩ := hgood (K + 1)
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  have h1 := hK m (by omega)
  have hP : 1 ≤ ∏ i ∈ range m, b i := Finset.one_le_prod' (fun k _ => hpos k)
  have h2 : b m ≤ 2 * M * ∏ i ∈ range (m + 1), b i := by
    rw [Finset.prod_range_succ]
    calc b m ≤ (∏ i ∈ range m, b i) * b m := Nat.le_mul_of_pos_left _ hP
      _ ≤ 2 * M * ((∏ i ∈ range m, b i) * b m) := Nat.le_mul_of_pos_left _ (by omega)
  have h3 : R ^ 2 ^ (m + 1) = (R ^ 2) ^ 2 ^ m := by rw [← pow_mul, pow_succ, mul_comm]
  omega

open Finset in
lemma e263_tail_le (b : ℕ → ℕ) (M P N : ℕ) (hM : 1 ≤ M) (hP : 1 ≤ P)
    (hT : ∀ n, M * 2 ^ n * P ≤ b (n + N)) :
    Summable (fun n => 1 / (b (n + N) : ℝ)) ∧ ∑' n, 1 / (b (n + N) : ℝ) ≤ 2 / (M * P) := by
  have hle : ∀ n, 1 / (b (n + N) : ℝ) ≤ (1 / (M * P)) * (1 / 2) ^ n := by
    intro n
    have h := hT n
    have hpos : (0 : ℝ) < M * 2 ^ n * P := by positivity
    have h' : (M * 2 ^ n * P : ℝ) ≤ b (n + N) := by exact_mod_cast h
    rw [one_div_pow, div_mul_div_comm, one_mul]
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have hg : Summable (fun n : ℕ => (1 / (M * P : ℝ)) * (1 / 2) ^ n) :=
    summable_geometric_two.mul_left _
  have hf : Summable (fun n => 1 / (b (n + N) : ℝ)) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hle hg
  refine ⟨hf, ?_⟩
  calc ∑' n, 1 / (b (n + N) : ℝ) ≤ ∑' n : ℕ, (1 / (M * P : ℝ)) * (1 / 2) ^ n :=
        Summable.tsum_le_tsum hle hf hg
    _ = 2 / (M * P) := by rw [tsum_mul_left, tsum_geometric_two]; ring

open Finset in
/-- Part A: the monotone case. -/
lemma e263_mono (b : ℕ → ℕ) (hmono : Monotone b) (hpos : ∀ k, 1 ≤ b k)
    (hG : ∀ R : ℕ, ∀ᶠ n in atTop, R ^ 2 ^ n < b n) :
    Summable (fun n => 1 / (b n : ℝ)) ∧ Irrational (∑' n, 1 / (b n : ℝ)) := by
  have hsum : Summable (fun n => 1 / (b n : ℝ)) := by
    obtain ⟨N, hN⟩ := e263_key b hmono hpos hG 1 le_rfl
    exact (summable_nat_add_iff N).mp
      (e263_tail_le b 1 _ N le_rfl (Finset.one_le_prod' (fun k _ => hpos k)) hN).1
  refine ⟨hsum, ?_⟩
  rintro ⟨r, hr⟩
  set q := r.den
  have hq : 1 ≤ q := r.den_pos
  obtain ⟨N, hN⟩ := e263_key b hmono hpos hG (2 * q + 1) (by omega)
  set P := ∏ k ∈ range N, b k with hPdef
  have hP : 1 ≤ P := Finset.one_le_prod' (fun k _ => hpos k)
  obtain ⟨hs, htail⟩ := e263_tail_le b (2 * q + 1) P N (by omega) hP hN
  set T := ∑' n, 1 / (b (n + N) : ℝ)
  have hsplit : ∑' n, 1 / (b n : ℝ) = ∑ i ∈ range N, 1 / (b i : ℝ) + T :=
    (hsum.sum_add_tsum_nat_add N).symm
  have hTpos : 0 < T := by
    apply hs.tsum_pos (fun n => by positivity) 0
    have := hpos (0 + N); positivity
  -- the integer z = q P T
  have hdvd : ∀ i ∈ range N, b i ∣ P := fun i hi => Finset.dvd_prod_of_mem _ hi
  have hz : (q : ℝ) * P * T = (r.num * P - q * ((∑ i ∈ range N, P / b i : ℕ) : ℤ) : ℤ) := by
    have hrq : (r : ℝ) * q = r.num := by
      have hd : (q : ℝ) ≠ 0 := by positivity
      rw [Rat.cast_def]; field_simp; rfl
    have hcast : ∀ i ∈ range N, ((P / b i : ℕ) : ℝ) = P * (1 / (b i : ℝ)) := by
      intro i hi
      have hb : (b i : ℝ) ≠ 0 := by have := hpos i; positivity
      rw [Nat.cast_div (hdvd i hi) hb]; field_simp
    have hT : T = r - ∑ i ∈ range N, 1 / (b i : ℝ) := by rw [hr, hsplit]; ring
    have hS : ((∑ i ∈ range N, P / b i : ℕ) : ℝ) = P * ∑ i ∈ range N, 1 / (b i : ℝ) := by
      rw [Nat.cast_sum, Finset.mul_sum]; exact Finset.sum_congr rfl hcast
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast]
    rw [hS, hT, ← hrq]
    ring
  set z : ℤ := r.num * P - q * ((∑ i ∈ range N, P / b i : ℕ) : ℤ)
  have hz1 : (0 : ℝ) < z := by rw [← hz]; positivity
  have hz2 : (z : ℝ) < 1 := by
    rw [← hz]
    have hPr : (0 : ℝ) < P := by exact_mod_cast hP
    calc (q : ℝ) * P * T ≤ q * P * (2 / ((2 * q + 1 : ℕ) * P)) := by gcongr
      _ = 2 * q / (2 * q + 1) := by push_cast; field_simp
      _ < 1 := by rw [div_lt_one (by positivity)]; linarith
  have h1 : (0 : ℤ) < z := by exact_mod_cast hz1
  have h2 : z < (1 : ℤ) := by exact_mod_cast hz2
  omega

open Finset in
/-- Part B: sort a sequence tending to infinity. -/
lemma e263_sort (a : ℕ → ℕ) (hfin : ∀ v, {n | a n ≤ v}.Finite) :
    ∃ σ : ℕ ≃ ℕ, Monotone (a ∘ σ) := by
  let key : ℕ → ℕ ×ₗ ℕ := fun n => toLex (a n, n)
  let D : ℕ → Set ℕ := fun n => {k | key k < key n}
  have hDfin : ∀ n, (D n).Finite := by
    intro n
    apply (hfin (a n)).subset
    intro k hk
    simp only [D, key, Set.mem_setOf_eq, Prod.Lex.toLex_lt_toLex] at hk ⊢
    omega
  let rank : ℕ → ℕ := fun n => (D n).ncard
  have hstrict : ∀ m n, key m < key n → rank m < rank n := by
    intro m n h
    apply Set.ncard_lt_ncard _ (hDfin n)
    refine ⟨fun k hk => lt_trans hk h, fun hsub => ?_⟩
    have : m ∈ D m := hsub h
    exact lt_irrefl (key m) this
  have hkeyinj : ∀ m n, key m = key n → m = n := by
    intro m n h
    simpa [key] using congrArg (fun x => (ofLex x).2) h
  have hinj : Function.Injective rank := by
    intro m n h
    rcases lt_trichotomy (key m) (key n) with h' | h' | h'
    · exact absurd h (hstrict m n h').ne
    · exact hkeyinj m n h'
    · exact absurd h (hstrict n m h').ne'
  have hle : ∀ m n, rank m ≤ rank n → a m ≤ a n := by
    intro m n h
    have : ¬ key n < key m := fun h' => absurd h (not_le.mpr (hstrict n m h'))
    simp only [key, Prod.Lex.toLex_lt_toLex, not_or, not_and, not_lt] at this
    omega
  have hdown : ∀ n, rank '' D n = Set.Iio (rank n) := by
    intro n
    apply Set.eq_of_subset_of_ncard_le
    · rintro _ ⟨k, hk, rfl⟩
      exact hstrict k n hk
    · rw [Set.ncard_image_of_injective _ hinj, Nat.ncard_Iio]
    · exact Set.finite_Iio _
  have hsurj : Function.Surjective rank := by
    intro r
    have hinf : (Set.range rank).Infinite := Set.infinite_range_of_injective hinj
    obtain ⟨_, ⟨n, rfl⟩, hn⟩ := hinf.exists_gt r
    have : r ∈ rank '' D n := by rw [hdown n]; exact hn
    obtain ⟨k, _, hk⟩ := this
    exact ⟨k, hk⟩
  refine ⟨(Equiv.ofBijective rank ⟨hinj, hsurj⟩).symm, ?_⟩
  intro i j hij
  apply hle
  have h1 := (Equiv.ofBijective rank ⟨hinj, hsurj⟩).apply_symm_apply i
  have h2 := (Equiv.ofBijective rank ⟨hinj, hsurj⟩).apply_symm_apply j
  change rank _ = i at h1
  change rank _ = j at h2
  rw [h1, h2]; exact hij

open Finset in
lemma e263_G (a : ℕ → ℕ)
    (ha : atTop.Tendsto (fun n : ℕ => (a n : ℝ) ^ (1 / (2 ^ n : ℝ))) atTop) :
    ∀ R : ℕ, ∀ᶠ n in atTop, R ^ 2 ^ n < a n := by
  intro R
  filter_upwards [ha.eventually_gt_atTop (R : ℝ)] with n hn
  have hx : (a n : ℝ) = ((a n : ℝ) ^ (1 / (2 ^ n : ℝ))) ^ (2 ^ n : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    push_cast
    rw [one_div_mul_cancel (by positivity), Real.rpow_one]
  have : (R : ℝ) ^ (2 ^ n : ℕ) < (a n : ℝ) := by
    rw [hx]
    exact pow_lt_pow_left₀ hn (Nat.cast_nonneg _) (by positivity)
  exact_mod_cast this

open Finset in
lemma e263_pigeon (σ : ℕ ≃ ℕ) (k : ℕ) : ∃ i ≤ k, k ≤ σ i := by
  by_contra h
  push_neg at h
  have := Finset.card_le_card_of_injOn σ (s := range (k + 1)) (t := range k)
    (fun i hi => by simp only [coe_range, Set.mem_Iio] at hi ⊢; exact h i (by omega))
    (σ.injective.injOn)
  simp at this

open Finset in
lemma e263_G_of_one (f : ℕ → ℕ) (h : ∀ R : ℕ, 1 ≤ R → ∀ᶠ n in atTop, R ^ 2 ^ n < f n) :
    ∀ R : ℕ, ∀ᶠ n in atTop, R ^ 2 ^ n < f n := by
  intro R
  rcases Nat.eq_zero_or_pos R with rfl | hR
  · filter_upwards [h 1 le_rfl] with n hn
    simp at hn ⊢; omega
  · exact h R hR

open Finset in
theorem e263_folklore_G (a : ℕ → ℕ) (hG : ∀ R : ℕ, ∀ᶠ n in atTop, R ^ 2 ^ n < a n) :
    Irrational <| ∑' n, (1 : ℝ) / (a n : ℝ) := by
  have hfin : ∀ v, {n | a n ≤ v}.Finite := by
    intro v
    obtain ⟨K, hK⟩ := (hG (v + 1)).exists_forall_of_atTop
    apply (Set.finite_Iio K).subset
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    simp only [Set.mem_Iio]
    by_contra hKn
    have h1 := hK n (by omega)
    have h2 : v + 1 ≤ (v + 1) ^ 2 ^ n := Nat.le_self_pow (by positivity) _
    omega
  obtain ⟨σ, hσ⟩ := e263_sort a hfin
  set b := a ∘ σ with hb
  have hGb : ∀ R : ℕ, ∀ᶠ k in atTop, R ^ 2 ^ k < b k := by
    apply e263_G_of_one
    intro R hR
    obtain ⟨K, hK⟩ := (hG R).exists_forall_of_atTop
    filter_upwards [eventually_ge_atTop K] with k hk
    obtain ⟨i, hik, hki⟩ := e263_pigeon σ k
    calc R ^ 2 ^ k ≤ R ^ 2 ^ (σ i) := Nat.pow_le_pow_right hR (Nat.pow_le_pow_right (by norm_num) hki)
      _ < a (σ i) := hK _ (by omega)
      _ = b i := rfl
      _ ≤ b k := hσ hik
  obtain ⟨k0, hk0⟩ := (hGb 1).exists_forall_of_atTop
  set c : ℕ → ℕ := fun k => b (k + k0) with hc
  have hcmono : Monotone c := fun i j hij => hσ (by omega)
  have hcpos : ∀ k, 1 ≤ c k := by
    intro k; have := hk0 (k + k0) (by omega); simp at this; simp only [c]; omega
  have hGc : ∀ R : ℕ, ∀ᶠ k in atTop, R ^ 2 ^ k < c k := by
    apply e263_G_of_one
    intro R hR
    obtain ⟨K, hK⟩ := (hGb R).exists_forall_of_atTop
    filter_upwards [eventually_ge_atTop K] with k hk
    calc R ^ 2 ^ k ≤ R ^ 2 ^ (k + k0) := Nat.pow_le_pow_right hR (Nat.pow_le_pow_right (by norm_num) (by omega))
      _ < b (k + k0) := hK _ (by omega)
  obtain ⟨hcs, hci⟩ := e263_mono c hcmono hcpos hGc
  have hbs : Summable (fun k => 1 / (b k : ℝ)) := (summable_nat_add_iff k0).mp hcs
  have h1 : ∑' n, (1 : ℝ) / (a n : ℝ) = ∑' k, 1 / (b k : ℝ) :=
    (Equiv.tsum_eq σ (fun n => (1 : ℝ) / (a n : ℝ))).symm
  have h2 : ∑' k, 1 / (b k : ℝ) = ∑ k ∈ range k0, 1 / (b k : ℝ) + ∑' k, 1 / (c k : ℝ) :=
    (hbs.sum_add_tsum_nat_add k0).symm
  rw [h1, h2]
  have h3 : ((∑ k ∈ range k0, 1 / (b k : ℚ) : ℚ) : ℝ) = ∑ k ∈ range k0, 1 / (b k : ℝ) := by
    push_cast; rfl
  rw [← h3]
  exact irrational_ratCast_add_iff.mpr hci

open Finset in
lemma e263_ev_G (a : ℕ → ℕ) (hpos : ∀ n, a n > 0) (hmono : StrictMono a) (ε c : ℝ) (hε : 0 < ε)
    (hc : 0 < c) (hg : ∀ᶠ n in atTop, c * (a n : ℝ) ^ (2 + ε) ≤ (a (n + 1) : ℝ)) :
    ∀ R : ℕ, ∀ᶠ n in atTop, R ^ 2 ^ n < a n := by
  set x : ℕ → ℝ := fun n => Real.log (a n) with hx
  have hapos : ∀ n, (0 : ℝ) < a n := fun n => by exact_mod_cast hpos n
  have hxt : atTop.Tendsto x atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmono.tendsto_atTop)
  have hstep : ∀ᶠ n in atTop, (2 + ε / 2) * x n ≤ x (n + 1) ∧ 1 ≤ x n := by
    filter_upwards [hg, hxt.eventually_ge_atTop (max 1 (-2 * Real.log c / ε))] with n hn hxn
    have h1 : Real.log c + (2 + ε) * x n ≤ x (n + 1) := by
      have := Real.log_le_log (by have := hapos n; positivity) hn
      rwa [Real.log_mul hc.ne' (by have := hapos n; positivity), Real.log_rpow (hapos n)] at this
    have h2 : -2 * Real.log c / ε ≤ x n := le_trans (le_max_right _ _) hxn
    have h3 : -2 * Real.log c ≤ ε * x n := by
      rw [div_le_iff₀ hε] at h2; linarith
    refine ⟨by nlinarith, le_trans (le_max_left _ _) hxn⟩
  obtain ⟨N, hN⟩ := hstep.exists_forall_of_atTop
  have hgrow : ∀ k, (2 + ε / 2) ^ k ≤ x (N + k) := by
    intro k
    induction k with
    | zero => simpa using (hN N le_rfl).2
    | succ k ih =>
      have := (hN (N + k) (by omega)).1
      rw [pow_succ, ← add_assoc]
      have hpos' : (0 : ℝ) ≤ (2 + ε / 2) ^ k := by positivity
      nlinarith
  intro R
  rcases Nat.eq_zero_or_pos R with rfl | hR
  · exact Filter.Eventually.of_forall fun n => by simpa using hpos n
  have hratio : atTop.Tendsto (fun k : ℕ => ((2 + ε / 2) / 2) ^ k) atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by linarith)
  obtain ⟨K, hK⟩ := (hratio.eventually_gt_atTop (2 ^ N * Real.log R)).exists_forall_of_atTop
  rw [Filter.eventually_atTop]
  refine ⟨N + K, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = N + k := ⟨n - N, by omega⟩
  have h1 := hK k (by omega)
  have h2 := hgrow k
  have hlog : Real.log ((R : ℝ) ^ 2 ^ (N + k)) < Real.log (a (N + k)) := by
    rw [Real.log_pow]
    have : (2 : ℝ) ^ (N + k) * Real.log R < (2 + ε / 2) ^ k := by
      rw [div_pow] at h1
      rw [lt_div_iff₀ (by positivity)] at h1
      rw [pow_add]; linarith
    push_cast
    exact lt_of_lt_of_le this h2
  have := (Real.log_lt_log_iff (by positivity) (hapos _)).mp hlog
  exact_mod_cast this

open Finset in
theorem e263_eventual (a : ℕ → ℕ) (ha : ∀ n : ℕ, a n > 0) (ha' : StrictMono a)
    (ha'' : ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧
      ∀ᶠ n in atTop, c * (a n : ℝ) ^ (2 + ε) ≤ (a (n + 1) : ℝ)) :
    (∀ n : ℕ, a n > 0) ∧ StrictMono a ∧
    (∀ b : ℕ → ℕ, (∀ n : ℕ, b n > 0) ∧
      atTop.Tendsto (fun n : ℕ => (a n : ℝ) / (b n : ℝ)) (nhds 1) →
      Irrational (∑' n, 1 / (b n : ℝ))) := by
  obtain ⟨ε, c, hε, hc, hg⟩ := ha''
  have hGa := e263_ev_G a ha ha' ε c hε hc hg
  refine ⟨ha, ha', fun b ⟨hbpos, hlim⟩ => e263_folklore_G b ?_⟩
  apply e263_G_of_one
  intro R hR
  filter_upwards [hGa (2 * R), hlim.eventually (gt_mem_nhds one_lt_two)] with n h1 h2
  have hb : (0 : ℝ) < b n := by exact_mod_cast hbpos n
  rw [div_lt_iff₀ hb] at h2
  have h3 : a n < 2 * b n := by exact_mod_cast h2
  have h4 : 2 * R ^ 2 ^ n ≤ (2 * R) ^ 2 ^ n := by
    rw [mul_pow]
    have : 2 ≤ 2 ^ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ 2 ^ n := Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow
    exact Nat.mul_le_mul_right _ this
  omega

/--
The same folklore result with the growth hypothesis stated as an eventual lower bound
$a_{n+1} \geq c\, a_n^{2+\varepsilon}$. Unlike the real-valued `liminf` in
`erdos_263.variants.super_doubly_exponential`, this form also covers sequences such as
$a_n = 2^{(n+1)!}$, for which the ratio $a_{n+1} / a_n^{2+\varepsilon}$ tends to $+\infty$ and the
real `liminf` defaults to $0$.
-/
@[category research solved, AMS 11]
theorem erdos_263.variants.super_doubly_exponential_eventual (a : ℕ → ℕ)
    (ha : ∀ n : ℕ, a n > 0)
    (ha' : StrictMono a)
    (ha'' : ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧
      ∀ᶠ n in atTop, c * (a n : ℝ) ^ (2 + ε) ≤ (a (n + 1) : ℝ)) :
    IsIrrationalitySequence a := by
  exact e263_eventual a ha ha' ha''

/--
Koizumi [Ko25] showed that $a_n = \lfloor \alpha^{2^n} \rfloor$ is an irrationality sequence
for all but countably many $\alpha > 1$, in the nondecreasing sense `IsWeakIrrationalitySequence`.
The strictly increasing predicate would fail on the whole interval $1 < \alpha < 4/3$, where
$a_0 = a_1 = 1$.

[Ko25] Koizumi, J., Irrationality of the reciprocal sum of doubly exponential sequences,
       arXiv:2504.05933 (2025).
-/
@[category research solved, AMS 11]
theorem erdos_263.variants.doubly_exponential_all_but_countable :
    ∀ᶠ (α : ℝ) in .cocountable, α > 1 →
      IsWeakIrrationalitySequence (fun n : ℕ => ⌊α ^ 2 ^ n⌋₊) := by
  sorry

end Erdos263
