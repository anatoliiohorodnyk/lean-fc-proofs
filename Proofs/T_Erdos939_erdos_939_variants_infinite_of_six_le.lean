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
# Erdős Problem 939

*References:*
- [erdosproblems.com/939](https://www.erdosproblems.com/939)
- [Ni95] Nitaj, A., _On a conjecture of Erdős on 3-powerful numbers_. Bull. London Math. Soc.
  (1995), 317-318.
- [Co98] Cohn, J. H. E., _A conjecture of Erdős on 3-powerful numbers_. Math. Comp. (1998),
  439-440.
- [Wa24] Walsh, P., _A question of Erdős on 3-powerful numbers and an elliptic curve analogue
  of the Ankeny-Artin-Chowla conjecture_. arXiv:2404.03970 (2024).
- [LaPa67] Lander, L. J. and Parkin, T. R., _A counterexample to Euler's sum of powers
  conjecture_. Math. Comp. (1967), 101-103.
-/

@[expose] public section

open Nat

namespace Erdos939

/--
A set `S` belongs to `Erdos939Sums r` if it meets the following criteria:
- The elements are positive. `0` has no prime factors, so it is vacuously `r`-powerful, and
  the source means positive integers.
- The size of the set is `$|S| = r - 2$`.
- The elements of the set are coprime (their greatest common divisor is 1).
- Every element in `S` is an `$r$-powerful` number.
- The sum of the elements in `S`, i.e., `$\sum_{s \in S} s$`, is also an `$r$-powerful` number.

The summands are taken to be distinct (`S` is a `Finset`). The source does not say whether
repeated summands are allowed; all known examples and constructions use distinct summands.
-/
def Erdos939Sums (r : ℕ) :=
    {S : Finset ℕ | S.card = r - 2 ∧ S.Coprime ∧ r.Full (∑ s ∈ S, s) ∧
      ∀ s ∈ S, 0 < s ∧ r.Full s}

/--
If $r≥4$ then can the sum of $r-2$ coprime $r$-powerful numbers ever be itself $r$-powerful?
-/
@[category research open, AMS 11]
theorem erdos_939 : answer(sorry) ↔ ∀ r ≥ 4, (Erdos939Sums r).Nonempty := by
  sorry

/--
If $r≥4$, are there at most finitely many sums of $r-2$ coprime $r$-powerful numbers
that are themselves $r$-powerful?

The answer is no: for every $r \ge 6$ there are infinitely many such sums, see
`erdos_939.variants.infinite_of_six_le`. (For $r = 4$ and $r = 5$ the question is open; for
$r = 4$ no example is known at all, see `erdos_939`.)
A construction in the site's comments, from GPT-5.5 Pro prompted by Price, gives infinitely
many for every $r \ge 6$. This statement quantifies over every $r \ge 4$, so it stays open at
$r = 4$ and $r = 5$. The category is unchanged because the construction is recorded in the
comments and not in the literature.
-/
@[category research solved, AMS 11]
theorem erdos_939.variants.finite : answer(False) ↔ ∀ r ≥ 4, (Erdos939Sums r).Finite := by
  sorry

open Finset in
lemma e939_split (f : ℕ → ℤ) (N : ℕ) :
    ∑ j ∈ range (2 * N), f j = ∑ m ∈ range N, f (2 * m) + ∑ m ∈ range N, f (2 * m + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, sum_range_succ]
    ring

open Finset in
lemma e939_binom (X Y : ℤ) (r : ℕ) (hr : 1 ≤ r) :
    (X + Y) ^ r = (X - Y) ^ r +
      ∑ m ∈ range r, 2 * (r.choose (2 * m + 1) : ℤ) * X ^ (r - (2 * m + 1)) * Y ^ (2 * m + 1) := by
  have h1 : (X + Y) ^ r = ∑ j ∈ range (2 * r), Y ^ j * X ^ (r - j) * (r.choose j : ℤ) := by
    rw [add_comm, add_pow]
    apply sum_subset (by intro j; simp only [mem_range]; omega)
    intro j _ hj
    simp only [mem_range, not_lt] at hj
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  have h2 : (X - Y) ^ r = ∑ j ∈ range (2 * r), (-Y) ^ j * X ^ (r - j) * (r.choose j : ℤ) := by
    rw [sub_eq_neg_add, add_pow]
    apply sum_subset (by intro j; simp only [mem_range]; omega)
    intro j _ hj
    simp only [mem_range, not_lt] at hj
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  rw [h1, h2, e939_split, e939_split]
  have he : ∀ m, (-Y) ^ (2 * m) = Y ^ (2 * m) := fun m => by rw [pow_mul, pow_mul, neg_sq]
  have ho : ∀ m, (-Y) ^ (2 * m + 1) = - Y ^ (2 * m + 1) := fun m => by
    rw [pow_succ, he, pow_succ]; ring
  simp only [he, ho]
  rw [← sub_eq_iff_eq_add']
  rw [show ∀ a b c : ℤ, a + b - (a + c) = b - c from fun a b c => by ring]
  rw [← sum_sub_distrib]
  apply sum_congr rfl; intro m _; ring

open Finset in
lemma e939_full_mul_pow (r a b : ℕ) (h : ∀ p, p.Prime → p ∣ a → p ∣ b) :
    r.Full (a * b ^ r) := by
  intro p hp
  rw [Nat.mem_primeFactors] at hp
  obtain ⟨hpp, hpd, -⟩ := hp
  have hpb : p ∣ b := by
    rcases (Nat.Prime.dvd_mul hpp).mp hpd with h1 | h1
    · exact h _ hpp h1
    · exact hpp.dvd_of_dvd_pow h1
  exact (pow_dvd_pow_of_dvd hpb r).trans (dvd_mul_left _ _)

open Finset in
lemma e939_full_pow (r m : ℕ) : r.Full (m ^ r) := by
  have := e939_full_mul_pow r 1 m (fun p hp h => absurd (Nat.dvd_one.mp h) hp.ne_one)
  simpa using this

open Finset in
lemma e939_geom (d : ℕ) : ∑ i ∈ range d, 2 ^ i = 2 ^ d - 1 := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [sum_range_succ, ih, pow_succ]
    have : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    omega

open Finset in
lemma e939_powlt (X Y c k : ℕ) (hk : 1 ≤ k) (hc : 1 ≤ c) (hY : 0 < Y) (h : c * Y < X) :
    c * Y ^ k < X ^ k := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0; simpa using h
    · have ih' := ih h0
      have hYX : Y ≤ X := by nlinarith
      calc c * Y ^ (k + 1) = c * Y ^ k * Y := by ring
        _ < X ^ k * Y := Nat.mul_lt_mul_of_pos_right ih' hY
        _ ≤ X ^ (k + 1) := by rw [pow_succ]; exact Nat.mul_le_mul_left _ hYX

open Finset in
lemma e939_dec (X Y c a b k C C' : ℕ) (hk : 1 ≤ k) (hc : 1 ≤ c) (hC : 1 ≤ C) (hC' : C' ≤ c) (hY : 0 < Y)
    (h : c * Y < X) : 2 * C' * X ^ a * Y ^ (b + k) < 2 * C * X ^ (a + k) * Y ^ b := by
  have hX : 0 < X := by omega
  have hkey : c * Y ^ k < X ^ k := e939_powlt X Y c k hk hc hY h
  calc 2 * C' * X ^ a * Y ^ (b + k) = 2 * C' * (X ^ a * Y ^ b) * Y ^ k := by ring
    _ ≤ 2 * c * (X ^ a * Y ^ b) * Y ^ k := by gcongr
    _ = 2 * (X ^ a * Y ^ b) * (c * Y ^ k) := by ring
    _ < 2 * (X ^ a * Y ^ b) * X ^ k := Nat.mul_lt_mul_of_pos_left hkey (by positivity)
    _ ≤ C * (2 * (X ^ a * Y ^ b) * X ^ k) := Nat.le_mul_of_pos_left _ hC
    _ = 2 * C * X ^ (a + k) * Y ^ b := by ring

open Finset in
def e939d (r : ℕ) : ℕ := r / 2 - 2
open Finset in
def e939g (r : ℕ) : ℕ := 2 ^ e939d r - 1
open Finset in
def e939B1 (r : ℕ) : ℕ := 2 * r.factorial * e939g r
open Finset in
def e939B (r : ℕ) : ℕ := e939g r * e939B1 r
open Finset in
def e939T (r q j : ℕ) : ℕ := 2 * r.choose j * (q ^ r) ^ (r - j) * (e939B r ^ r) ^ j
open Finset in
def e939K (r q : ℕ) : ℕ := 2 * r * q ^ (r * (r - 1)) * e939g r ^ (r - 1) * e939B1 r ^ r
open Finset in
def e939A (r q : ℕ) : ℕ := (q ^ r - e939B r ^ r) ^ r
open Finset in
def e939S (r q : ℕ) : Finset ℕ :=
  insert (e939A r q) ((range (e939d r)).image (fun i => 2 ^ i * e939K r q) ∪
    (range ((r - 1) / 2)).image (fun m => e939T r q (2 * m + 3)))

open Finset in
lemma e939g_pos (r : ℕ) (hr : 6 ≤ r) : 1 ≤ e939g r := by
  unfold e939g e939d
  have : 2 ≤ 2 ^ (r / 2 - 2) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (r / 2 - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

open Finset in
lemma e939g_lt (r : ℕ) : e939g r < 2 ^ r := by
  unfold e939g e939d
  have : 2 ^ (r / 2 - 2) ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : 1 ≤ 2 ^ (r / 2 - 2) := Nat.one_le_two_pow
  omega

open Finset in
lemma e939B_pos (r : ℕ) (hr : 6 ≤ r) : 0 < e939B r := by
  unfold e939B e939B1
  have := e939g_pos r hr
  have := Nat.factorial_pos r
  positivity

open Finset in
lemma e939_dvdB1 (r p : ℕ) (hp : p.Prime) (h : p ∣ 2 ∨ p ∣ r.factorial ∨ p ∣ e939g r) :
    p ∣ e939B1 r := by
  unfold e939B1
  rcases h with h | h | h
  · exact (h.mul_right _).mul_right _
  · exact (h.mul_left _).mul_right _
  · exact h.mul_left _

open Finset in
lemma e939_B1_dvd_B (r : ℕ) : e939B1 r ∣ e939B r := dvd_mul_left _ _

open Finset in
lemma e939_gK (r q : ℕ) (hr : 6 ≤ r) : e939g r * e939K r q = e939T r q 1 := by
  unfold e939K e939T e939B
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.choose_one_right, Nat.add_sub_cancel, pow_one]
  ring

open Finset in
lemma e939_sumT (r q : ℕ) (hr : 6 ≤ r) (hXY : e939B r ^ r ≤ q ^ r) :
    e939A r q + e939T r q 1 + ∑ m ∈ range ((r - 1) / 2), e939T r q (2 * m + 3) =
      (q ^ r + e939B r ^ r) ^ r := by
  zify [hXY]
  have hb := e939_binom ((q : ℤ) ^ r) ((e939B r : ℤ) ^ r) r (by omega)
  have hT : ∀ j, ((e939T r q j : ℕ) : ℤ) =
      2 * (r.choose j : ℤ) * ((q : ℤ) ^ r) ^ (r - j) * ((e939B r : ℤ) ^ r) ^ j := by
    intro j; unfold e939T; push_cast; ring
  unfold e939A
  push_cast
  rw [hb]
  obtain ⟨s, hs⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have hsplit : ∑ m ∈ range r, 2 * (r.choose (2 * m + 1) : ℤ) * ((q : ℤ) ^ r) ^ (r - (2 * m + 1)) *
      ((e939B r : ℤ) ^ r) ^ (2 * m + 1) =
      ((e939T r q 1 : ℕ) : ℤ) + ∑ m ∈ range ((r - 1) / 2), ((e939T r q (2 * m + 3) : ℕ) : ℤ) := by
    have h1 : range r = range (s + 1) := by rw [hs]
    rw [h1, sum_range_succ', add_comm]
    simp only [hT]
    simp_rw [show ∀ k : ℕ, 2 * (k + 1) + 1 = 2 * k + 3 from fun k => by ring]
    congr 1
    symm
    apply sum_subset (by intro m; simp only [mem_range]; omega)
    intro m hm hm'
    simp only [mem_range, not_lt] at hm hm'
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  rw [hsplit, Nat.cast_sub hXY]
  push_cast
  ring

open Finset in
lemma e939_XY (r q : ℕ) (hr : 6 ≤ r) (hqB : 4 * e939B r < q) :
    4 ^ r * e939B r ^ r < q ^ r := by
  rw [← mul_pow]; exact Nat.pow_lt_pow_left hqB (by omega)

open Finset in
lemma e939_choose_le (r j : ℕ) : r.choose j ≤ 4 ^ r :=
  (Nat.choose_le_two_pow r j).trans (Nat.pow_le_pow_left (by norm_num) r)

open Finset in
lemma e939_Tdec (r q m m' : ℕ) (hr : 6 ≤ r) (hqB : 4 * e939B r < q) (hmm : m < m')
    (hm' : 2 * m' + 3 ≤ r) : e939T r q (2 * m' + 3) < e939T r q (2 * m + 3) := by
  have hY : 0 < e939B r ^ r := pow_pos (e939B_pos r hr) r
  have h := e939_dec (q ^ r) (e939B r ^ r) (4 ^ r) (r - (2 * m' + 3)) (2 * m + 3) (2 * (m' - m))
    (r.choose (2 * m + 3)) (r.choose (2 * m' + 3)) (by omega) (Nat.one_le_pow _ _ (by norm_num))
    (Nat.choose_pos (by omega)) (e939_choose_le _ _) hY (e939_XY r q hr hqB)
  calc e939T r q (2 * m' + 3) = 2 * r.choose (2 * m' + 3) * (q ^ r) ^ (r - (2 * m' + 3)) *
        (e939B r ^ r) ^ (2 * m + 3 + 2 * (m' - m)) := by
          unfold e939T; rw [show 2 * m + 3 + 2 * (m' - m) = 2 * m' + 3 by omega]
    _ < _ := h
    _ = e939T r q (2 * m + 3) := by
          unfold e939T; rw [show r - (2 * m' + 3) + 2 * (m' - m) = r - (2 * m + 3) by omega]

open Finset in
lemma e939_T3K (r q : ℕ) (hr : 6 ≤ r) (hqB : 4 * e939B r < q) : e939T r q 3 < e939K r q := by
  have hY : 0 < e939B r ^ r := pow_pos (e939B_pos r hr) r
  have hg := e939g_pos r hr
  have hcg : r.choose 3 * e939g r ≤ 4 ^ r := by
    calc r.choose 3 * e939g r ≤ 2 ^ r * 2 ^ r :=
          Nat.mul_le_mul (Nat.choose_le_two_pow r 3) (e939g_lt r).le
      _ = 4 ^ r := by rw [← mul_pow]; norm_num
  have h := e939_dec (q ^ r) (e939B r ^ r) (4 ^ r) (r - 3) 1 2 r (r.choose 3 * e939g r)
    (by omega) (Nat.one_le_pow _ _ (by norm_num)) (by omega) hcg hY (e939_XY r q hr hqB)
  have h2 : e939g r * e939T r q 3 < e939g r * e939K r q := by
    rw [e939_gK r q hr]
    calc e939g r * e939T r q 3 = 2 * (r.choose 3 * e939g r) * (q ^ r) ^ (r - 3) *
          (e939B r ^ r) ^ (1 + 2) := by unfold e939T; ring
      _ < _ := h
      _ = e939T r q 1 := by
          unfold e939T; rw [show r - 3 + 2 = r - 1 by omega, Nat.choose_one_right]
  exact Nat.lt_of_mul_lt_mul_left h2

open Finset in
lemma e939_Tle3 (r q m : ℕ) (hr : 6 ≤ r) (hqB : 4 * e939B r < q) (hm : m < (r - 1) / 2) :
    e939T r q (2 * m + 3) ≤ e939T r q 3 := by
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · subst h0; rfl
  · exact (e939_Tdec r q 0 m hr hqB h0 (by omega)).le

open Finset in
lemma e939_B_even (r : ℕ) : 2 ∣ e939B r := by
  unfold e939B e939B1; exact ((dvd_mul_right 2 _).mul_right _).mul_left _

open Finset in
lemma e939_K_even (r q : ℕ) : 2 ∣ e939K r q := by
  unfold e939K; exact (((dvd_mul_right 2 r).mul_right _).mul_right _).mul_right _

open Finset in
lemma e939_T_even (r q j : ℕ) : 2 ∣ e939T r q j := by
  unfold e939T; exact ((dvd_mul_right 2 _).mul_right _).mul_right _

open Finset in
lemma e939_A_odd (r q : ℕ) (hr : 6 ≤ r) (hq : q.Prime) (hqB : 4 * e939B r < q) :
    ¬ 2 ∣ e939A r q := by
  have hq2 : q ≠ 2 := by have := e939B_pos r hr; omega
  have hqo : Odd q := hq.odd_of_ne_two hq2
  have hXo : Odd (q ^ r) := hqo.pow
  have hYe : Even (e939B r ^ r) := (even_iff_two_dvd.mpr (e939_B_even r)).pow_of_ne_zero (by omega)
  have hle : e939B r ^ r ≤ q ^ r := (Nat.le_of_lt (lt_of_le_of_lt
    (Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ (by norm_num))) (e939_XY r q hr hqB)))
  have hd : Odd (q ^ r - e939B r ^ r) := by
    rcases hXo with ⟨a, ha⟩; rcases hYe with ⟨b, hb⟩
    exact ⟨a - b, by omega⟩
  unfold e939A
  rw [← even_iff_two_dvd, Nat.not_even_iff_odd]
  exact hd.pow

open Finset in
lemma e939_full_P (r q i : ℕ) (hr : 6 ≤ r) : r.Full (2 ^ i * e939K r q) := by
  have heq : 2 ^ i * e939K r q =
      (2 ^ (i + 1) * r * e939g r ^ (r - 1)) * (q ^ (r - 1) * e939B1 r) ^ r := by
    unfold e939K; rw [mul_pow, ← pow_mul, show (r - 1) * r = r * (r - 1) by ring]; ring
  rw [heq]
  apply e939_full_mul_pow
  intro p hp h
  apply Dvd.dvd.mul_left
  apply e939_dvdB1 r p hp
  rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
    · exact Or.inl (hp.dvd_of_dvd_pow h2)
    · exact Or.inr (Or.inl (h2.trans (Nat.dvd_factorial (by omega) le_rfl)))
  · exact Or.inr (Or.inr (hp.dvd_of_dvd_pow h1))

open Finset in
lemma e939_full_T (r q j : ℕ) (hj : 1 ≤ j) (hjr : j ≤ r) : r.Full (e939T r q j) := by
  have heq : e939T r q j = (2 * r.choose j) * (q ^ (r - j) * e939B r ^ j) ^ r := by
    unfold e939T; rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul]; ring
  rw [heq]
  apply e939_full_mul_pow
  intro p hp h
  apply Dvd.dvd.mul_left
  have hB : p ∣ e939B r := by
    apply (e939_dvdB1 r p hp _).trans (e939_B1_dvd_B r)
    rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
    · exact Or.inl h1
    · refine Or.inr (Or.inl (h1.trans ?_))
      exact ⟨j.factorial * (r - j).factorial, by
        rw [← mul_assoc]; exact (Nat.choose_mul_factorial_mul_factorial hjr).symm⟩
  exact hB.trans (dvd_pow_self _ (by omega))

open Finset in
lemma e939_coprime_AK (r q : ℕ) (hr : 6 ≤ r) (hq : q.Prime) (hqB : 4 * e939B r < q) :
    Nat.Coprime (e939A r q) (e939K r q) := by
  have hBpos := e939B_pos r hr
  have hle : e939B r ^ r ≤ q ^ r := (Nat.le_of_lt (lt_of_le_of_lt
    (Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ (by norm_num))) (e939_XY r q hr hqB)))
  apply Nat.coprime_of_dvd
  intro p hp hpA hpK
  have hpd : p ∣ q ^ r - e939B r ^ r := hp.dvd_of_dvd_pow hpA
  have hqB' : ¬ q ∣ e939B r := fun h => by have := Nat.le_of_dvd hBpos h; omega
  -- p divides q or B
  have hpqB : p ∣ q ∨ p ∣ e939B r := by
    unfold e939K at hpK
    rcases (Nat.Prime.dvd_mul hp).mp hpK with h1 | h1
    · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
      · rcases (Nat.Prime.dvd_mul hp).mp h2 with h3 | h3
        · right
          apply (e939_dvdB1 r p hp _).trans (e939_B1_dvd_B r)
          rcases (Nat.Prime.dvd_mul hp).mp h3 with h4 | h4
          · exact Or.inl h4
          · exact Or.inr (Or.inl (h4.trans (Nat.dvd_factorial (by omega) le_rfl)))
        · left; exact hp.dvd_of_dvd_pow h3
      · right
        exact (e939_dvdB1 r p hp (Or.inr (Or.inr (hp.dvd_of_dvd_pow h2)))).trans (e939_B1_dvd_B r)
    · right; exact (hp.dvd_of_dvd_pow h1).trans (e939_B1_dvd_B r)
  have hsum : q ^ r - e939B r ^ r + e939B r ^ r = q ^ r := Nat.sub_add_cancel hle
  rcases hpqB with h | h
  · have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp h
    have h2 : p ∣ q ^ r := dvd_pow h (by omega)
    rw [← hsum] at h2
    have h3 : p ∣ e939B r ^ r := (Nat.dvd_add_right hpd).mp h2
    exact hqB' (hpq ▸ hp.dvd_of_dvd_pow h3)
  · have h2 : p ∣ q ^ r := by
      rw [← hsum]; exact dvd_add hpd (dvd_pow h (by omega))
    have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow h2)
    exact hqB' (hpq ▸ h)

open Finset in
lemma e939_mem (r q : ℕ) (hr : 6 ≤ r) (hq : q.Prime) (hqB : 4 * e939B r < q) :
    e939S r q ∈ Erdos939Sums r ∧ ∑ s ∈ e939S r q, s = (q ^ r + e939B r ^ r) ^ r := by
  have hBpos := e939B_pos r hr
  have hg := e939g_pos r hr
  have hqpos : 0 < q := hq.pos
  have hK : 0 < e939K r q := by
    unfold e939K e939B1
    have := Nat.factorial_pos r
    positivity
  have hle : e939B r ^ r ≤ q ^ r := (Nat.le_of_lt (lt_of_le_of_lt
    (Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ (by norm_num))) (e939_XY r q hr hqB)))
  have injP : Set.InjOn (fun i => 2 ^ i * e939K r q) ↑(range (e939d r)) := by
    intro i _ j _ h
    exact Nat.pow_right_injective le_rfl (Nat.eq_of_mul_eq_mul_right hK h)
  have injT : Set.InjOn (fun m => e939T r q (2 * m + 3)) ↑(range ((r - 1) / 2)) := by
    intro m hm m' hm' h
    simp only [coe_range, Set.mem_Iio] at hm hm'
    simp only at h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := e939_Tdec r q m m' hr hqB hlt (by omega); omega
    · have := e939_Tdec r q m' m hr hqB hlt (by omega); omega
  have hdisj : Disjoint ((range (e939d r)).image (fun i => 2 ^ i * e939K r q))
      ((range ((r - 1) / 2)).image (fun m => e939T r q (2 * m + 3))) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [mem_image, mem_range] at hx hx'
    obtain ⟨i, -, rfl⟩ := hx
    obtain ⟨m, hm, hm2⟩ := hx'
    have h1 := e939_Tle3 r q m hr hqB hm
    have h2 := e939_T3K r q hr hqB
    have h3 : e939K r q ≤ 2 ^ i * e939K r q := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos i)
    omega
  have hA : e939A r q ∉ (range (e939d r)).image (fun i => 2 ^ i * e939K r q) ∪
      (range ((r - 1) / 2)).image (fun m => e939T r q (2 * m + 3)) := by
    intro h
    apply e939_A_odd r q hr hq hqB
    simp only [mem_union, mem_image, mem_range] at h
    rcases h with ⟨i, -, hi⟩ | ⟨m, -, hm⟩
    · rw [← hi]; exact (e939_K_even r q).mul_left _
    · rw [← hm]; exact e939_T_even r q _
  have hsum : ∑ s ∈ e939S r q, s = (q ^ r + e939B r ^ r) ^ r := by
    unfold e939S
    rw [sum_insert hA, sum_union hdisj, sum_image injP, sum_image injT, ← sum_mul, e939_geom,
      show 2 ^ e939d r - 1 = e939g r from rfl, e939_gK r q hr, ← add_assoc]
    exact e939_sumT r q hr hle
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hsum⟩
  · unfold e939S
    rw [Finset.card_insert_of_notMem hA, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn injP,
      Finset.card_image_of_injOn injT, card_range, card_range]
    unfold e939d; omega
  · show (e939S r q).gcd id = 1
    have hAm : e939A r q ∈ e939S r q := mem_insert_self _ _
    have hKm : e939K r q ∈ e939S r q := by
      unfold e939S
      refine mem_insert_of_mem (mem_union_left _ (mem_image.mpr ⟨0, ?_, by simp⟩))
      simp only [mem_range]; unfold e939d; omega
    exact Nat.eq_one_of_dvd_one ((e939_coprime_AK r q hr hq hqB) ▸
      Nat.dvd_gcd (Finset.gcd_dvd hAm) (Finset.gcd_dvd hKm))
  · rw [hsum]; exact e939_full_pow r _
  · intro s hs
    unfold e939S at hs
    simp only [mem_insert, mem_union, mem_image, mem_range] at hs
    rcases hs with rfl | ⟨i, -, rfl⟩ | ⟨m, hm, rfl⟩
    · refine ⟨?_, e939_full_pow r _⟩
      unfold e939A
      apply pow_pos
      have := e939_XY r q hr hqB
      have : e939B r ^ r < q ^ r := lt_of_le_of_lt
        (Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ (by norm_num))) this
      omega
    · exact ⟨by positivity, e939_full_P r q i hr⟩
    · refine ⟨?_, e939_full_T r q _ (by omega) (by omega)⟩
      unfold e939T
      have := Nat.choose_pos (show 2 * m + 3 ≤ r by omega)
      positivity

/--
For every $r \ge 6$ there are infinitely many sums of $r - 2$ coprime $r$-powerful numbers that
are themselves $r$-powerful.

A construction, found by GPT-5.5 Pro prompted by Liam Price and recorded in the comments on
[erdosproblems.com/939](https://www.erdosproblems.com/forum/thread/939), expands
$(X+Y)^r = (X-Y)^r + \sum_{j \text{ odd}} 2\binom{r}{j} X^{r-j} Y^j$, splits the $j = 3$ term into
$\lfloor r/2 \rfloor - 2$ distinct pieces to obtain exactly $r - 2$ summands, and takes
$X = q^r$, $Y = B^r$ with $B$ divisible by all primes in the coefficients and $q > B$ a prime not
dividing $B$; varying $q$ gives infinitely many solutions.
-/
@[category research solved, AMS 11]
theorem erdos_939.variants.infinite_of_six_le : ∀ r ≥ 6, (Erdos939Sums r).Infinite := by
  intro r hr
  have hs : {q | q.Prime ∧ 4 * e939B r < q}.Infinite := by
    apply Set.infinite_of_forall_exists_gt
    intro a
    obtain ⟨p, hp1, hp2⟩ := Nat.exists_infinite_primes (a + 4 * e939B r + 1)
    exact ⟨p, ⟨hp2, by omega⟩, by omega⟩
  refine Set.infinite_of_injOn_mapsTo (f := e939S r) ?_ ?_ hs
  · intro q hq q' hq' h
    have h1 := (e939_mem r q hr hq.1 hq.2).2
    have h2 := (e939_mem r q' hr hq'.1 hq'.2).2
    rw [h] at h1
    rw [h1] at h2
    have h3 := Nat.pow_left_injective (by omega : r ≠ 0) h2
    exact Nat.pow_left_injective (by omega : r ≠ 0) (by omega : q ^ r = q' ^ r)
  · intro q hq; exact (e939_mem r q hr hq.1 hq.2).1

/--
Are there infinitely many triples of coprime $3$-powerful numbers $a, b, c$ such that $a + b = c$?

The answer is yes. Nitaj [Ni95] proved it, with $2^3\cdot 3^5\cdot 73^3 + 271^3 = 919^3$ as an
example. In Nitaj's construction at least two of $a, b, c$ are perfect cubes. Cohn [Co98]
constructed infinitely many triples of which none is a perfect cube, and Walsh [Wa24] gave a
further construction.
-/
@[category research solved, AMS 11]
theorem erdos_939.variants.triples :
    answer(True) ↔ {(a,b,c) | ({a, b, c} : Finset ℕ).Coprime ∧
      0 < a ∧ 0 < b ∧
      (3).Full a ∧ (3).Full b ∧ (3).Full c ∧
      a + b = c}.Infinite := by
  sorry

/--
Cambie has found several examples of the sum of $r - 2$ coprime $r$-powerful numbers being itself
$r$-powerful. For example when $r=5$ we have
$$3^7\cdot 61^5 = 2^8\cdot3^{10}\cdot 5^7 + 2^{12}\cdot 23^6 + 11^5\cdot 13^5$$.
-/
@[category research solved, AMS 11]
theorem erdos_939.variants.examples : (∃ r ≥ 4, (Erdos939Sums r).Nonempty) := by
  use 5
  simp only [ge_iff_le, reduceLeDiff, true_and]
  unfold Erdos939Sums
  simp [Set.Nonempty]
  use {2^8 * 3^10 * 5^7, 2^12 * 23^6, 11^5 * 13^5}
  simp
  constructor
  · unfold Finset.Coprime
    aesop
  · norm_num [Nat.Full, Nat.primeFactors, Nat.primeFactorsList]


/-- Cambie has also found solutions when $r=7$. -/
@[category research solved, AMS 11]
theorem erdos_939.variants.seven : (Erdos939Sums 7).Nonempty := by
  sorry

/--
Cambie has also found solutions when $r=8$.

The source adds that the $r=8$ solution works "even with the sum of $5$ $8$-powerful numbers".
That is a stronger result than this statement, which asks for the $r - 2 = 6$ summands of
`Erdos939Sums`.
-/
@[category research solved, AMS 11]
theorem erdos_939.variants.eight : (Erdos939Sums 8).Nonempty := by
  sorry

/--
Euler had conjectured that the sum of $k - 1$ many $k$-th powers is never a
$k$-th power, but this is false for $k=5$, as Lander and Parkin [LaPa67] found
$$27^5+84^5+110^5+133^5=144^5$$.

The summands must be positive. Without that condition a set containing `0` would count, so the
negation would be satisfied by a sum of fewer than $k-1$ powers and would claim less than the
refutation of Euler's conjecture that this theorem records.
-/
@[category research solved, AMS 11]
theorem erdos_939.variants.euler : ¬ (∀ k ≥ 4, ∀ S : Finset ℕ, S.card = k - 1 →
    (∀ s ∈ S, 0 < s) → ¬ (∃ q, ∑ s ∈ S, s ^ k = q ^k)) := by
  push Not
  use 5
  norm_num
  use {27, 84, 110, 133}
  refine ⟨by decide, by decide, 144, by norm_num⟩

end Erdos939
