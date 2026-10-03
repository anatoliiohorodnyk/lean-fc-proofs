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
# Erdős Problem 889

*Reference:* [erdosproblems.com/889](https://www.erdosproblems.com/889)
-/

@[expose] public section

open Finset Nat Filter Topology

namespace Erdos889

/--
$v(n,k)$ counts the prime factors of $n+k$ which do not divide $n+i$
for all $0 \le i < k$.
-/
def v (n k : ℕ) : ℕ :=
  ((n + k).primeFactors.filter (fun p =>
    ∀ i ∈ range k, ¬ p ∣ n + i)).card

/--
$v_0(n)$ is the supremum of $v(n,k)$ for all $k \ge 0$.
-/
noncomputable def v₀ (n : ℕ) : ℕ∞ :=
  ⨆ k, (v n k : ℕ∞)

/--
Let $v(n,k)$ count the prime factors of $n+k$ which
do not divide $n+i$ for $0\leq i < k$. Is it true that
$v_0(n)=\max_{k\geq 0}v(n,k)\to \infty$ as $n\to \infty$?
-/
@[category research open, AMS 11]
theorem erdos_889 : Tendsto v₀ atTop (𝓝 ⊤) := by
  sorry

lemma e889_pow3_mod80 (m : ℕ) :
    3 ^ m % 80 = 1 ∨ 3 ^ m % 80 = 3 ∨ 3 ^ m % 80 = 9 ∨ 3 ^ m % 80 = 27 := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, Nat.mul_mod]; rcases ih with h | h | h | h <;> rw [h] <;> norm_num

lemma e889_pow2_mod80 (b : ℕ) :
    2 ^ (b + 4) % 80 = 16 ∨ 2 ^ (b + 4) % 80 = 32 ∨ 2 ^ (b + 4) % 80 = 64 ∨
      2 ^ (b + 4) % 80 = 48 := by
  induction b with
  | zero => norm_num
  | succ b ih =>
    rw [show b + 1 + 4 = (b + 4) + 1 by ring, pow_succ, Nat.mul_mod]
    rcases ih with h | h | h | h <;> rw [h] <;> norm_num

lemma e889_pow3_mod8 (m : ℕ) : 3 ^ m % 8 = 1 ∨ 3 ^ m % 8 = 3 := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, Nat.mul_mod]; rcases ih with h | h <;> rw [h] <;> norm_num

lemma e889_cat1 (b m : ℕ) (h : 2 ^ b + 1 = 3 ^ m) : b ≤ 3 := by
  by_contra hb
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 4 := ⟨b - 4, by omega⟩
  have h1 := e889_pow3_mod80 m
  have h2 := e889_pow2_mod80 c
  rw [← h] at h1
  generalize 2 ^ (c + 4) = X at h1 h2
  omega

lemma e889_cat2 (b m : ℕ) (h : 3 ^ m + 1 = 2 ^ b) : b ≤ 2 := by
  by_contra hb
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 3 := ⟨b - 3, by omega⟩
  have h1 := e889_pow3_mod8 m
  have h2 : 2 ^ (c + 3) % 8 = 0 := by
    rw [pow_add]; exact Nat.mul_mod_left _ _
  rw [← h] at h2
  generalize 3 ^ m = X at h1 h2
  omega

lemma e889_dvd_diff (q x d : ℕ) (h1 : q ∣ x) (h2 : q ∣ x + d) : q ∣ d :=
  (Nat.dvd_add_right h1).mp h2

/--
$v_0(n) > 1$ for all $n$ except $n$ = 0, 1, 2, 3, 4, 7, 8, 16

[ErSe67] Erdős, P. and Selfridge, J. L., Some problems on the prime factors of consecutive integers. Illinois J. Math. (1967), 428--430.
-/
@[category research solved, AMS 11]
theorem erdos_889.variants.v0_gt_1 :
    ∀ n : ℕ, n ∉ ({0, 1, 2, 3, 4, 7, 8, 16} : Finset ℕ) → 1 < v₀ n := by
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  by_contra hcon
  have H : ∀ k, v n k ≤ 1 := by
    intro k
    have : (v n k : ℕ∞) ≤ 1 :=
      (le_iSup (fun k => (v n k : ℕ∞)) k).trans (not_lt.mp hcon)
    exact_mod_cast this
  have uniq : ∀ k p q, p.Prime → p ∣ n + k → (∀ i ∈ range k, ¬ p ∣ n + i) →
      q.Prime → q ∣ n + k → (∀ i ∈ range k, ¬ q ∣ n + i) → q = p := by
    intro k p q hp hpd hp' hq hqd hq'
    have h := H k
    unfold v at h
    exact Finset.card_le_one.mp h q
      (Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hq, hqd, by omega⟩, hq'⟩) p
      (Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, hpd, by omega⟩, hp'⟩)
  have hn0 : n ≠ 0 := by omega
  have nd1 : ∀ q, q.Prime → q ∣ n → ¬ q ∣ n + 1 := fun q hq h1 h2 =>
    hq.one_lt.ne' (Nat.dvd_one.mp (e889_dvd_diff q n 1 h1 h2))
  have nd1' : ∀ q, q.Prime → q ∣ n + 1 → ¬ q ∣ n + 2 := fun q hq h1 h2 =>
    hq.one_lt.ne' (Nat.dvd_one.mp (e889_dvd_diff q (n + 1) 1 h1 (by simpa [add_assoc] using h2)))
  have nd2 : ∀ q, q.Prime → q ∣ n → q ∣ n + 2 → q = 2 := fun q hq h1 h2 =>
    (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (e889_dvd_diff q n 2 h1 h2)
  rcases Nat.even_or_odd n with he | ho
  · -- n is a power of two
    have h2n : 2 ∣ n := he.two_dvd
    obtain ⟨a, hpow⟩ : ∃ a, n = 2 ^ a :=
      ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hn0 (fun {q} hq hd =>
        uniq 0 2 q Nat.prime_two h2n (by simp) hq hd (by simp))⟩
    have h3n : ¬ 3 ∣ n := by
      intro h3
      rw [hpow] at h3
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow h3)
      omega
    have hmod : n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases hmod with h | h
    · -- 3 ∣ n + 2
      have h3 : 3 ∣ n + 2 := by omega
      have ha1 : 1 ≤ a := by
        rcases Nat.eq_zero_or_pos a with h0 | h0
        · rw [h0] at hpow; omega
        · exact h0
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      have hnc : n + 2 = 2 * (2 ^ a' + 1) := by rw [hpow, pow_succ]; ring
      have hcodd : ¬ 2 ∣ 2 ^ a' + 1 := by
        intro h2c
        rcases Nat.eq_zero_or_pos a' with h0 | h0
        · subst h0; simp at hpow; omega
        · have : 2 ∣ 2 ^ a' := dvd_pow_self 2 (by omega)
          omega
      have h3c : 3 ∣ 2 ^ a' + 1 := by
        rw [hnc] at h3
        exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h3)
      have cond : ∀ q, q.Prime → q ∣ 2 ^ a' + 1 → ∀ i ∈ range 2, ¬ q ∣ n + i := by
        intro q hq hqc i hi
        have hqn2 : q ∣ n + 2 := hnc ▸ Dvd.dvd.mul_left hqc 2
        have hq2 : q ≠ 2 := by rintro rfl; exact hcodd hqc
        simp only [Finset.mem_range] at hi
        interval_cases i
        · intro hd; exact hq2 (nd2 q hq hd hqn2)
        · intro hd; exact nd1' q hq hd hqn2
      obtain ⟨m, hcpow⟩ : ∃ m, 2 ^ a' + 1 = 3 ^ m :=
        ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (by omega) (fun {q} hq hd =>
          uniq 2 3 q Nat.prime_three h3 (cond 3 Nat.prime_three h3c) hq
            (hnc ▸ Dvd.dvd.mul_left hd 2) (cond q hq hd))⟩
      have := e889_cat1 a' m hcpow
      interval_cases a' <;> simp at hpow <;> omega
    · -- 3 ∣ n + 1
      have h3 : 3 ∣ n + 1 := by omega
      obtain ⟨m, hpow1⟩ : ∃ m, n + 1 = 3 ^ m :=
        ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (by omega) (fun {q} hq hd =>
          uniq 1 3 q Nat.prime_three h3 (by simpa using h3n)
            hq hd (by simpa using fun h => nd1 q hq h hd))⟩
      have := e889_cat1 a m (hpow ▸ hpow1)
      interval_cases a <;> simp at hpow <;> omega
  · -- n + 1 is a power of two
    have h2n : 2 ∣ n + 1 := by rcases ho with ⟨t, rfl⟩; exact ⟨t + 1, by ring⟩
    obtain ⟨b, hpow⟩ : ∃ b, n + 1 = 2 ^ b :=
      ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (by omega) (fun {q} hq hd =>
        uniq 1 2 q Nat.prime_two h2n (by simpa using fun h => nd1 2 Nat.prime_two h h2n)
          hq hd (by simpa using fun h => nd1 q hq h hd))⟩
    have hmod : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases hmod with h | h | h
    · have h3 : 3 ∣ n := by omega
      obtain ⟨m, hpow0⟩ : ∃ m, n = 3 ^ m :=
        ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hn0 (fun {q} hq hd =>
          uniq 0 3 q Nat.prime_three h3 (by simp) hq hd (by simp))⟩
      have := e889_cat2 b m (by rw [← hpow0, hpow])
      interval_cases b <;> simp at hpow <;> omega
    · have h3 : 3 ∣ n + 2 := by omega
      have cond : ∀ q, q.Prime → q ∣ n + 2 → ∀ i ∈ range 2, ¬ q ∣ n + i := by
        intro q hq hqn2 i hi
        simp only [Finset.mem_range] at hi
        interval_cases i
        · intro hd
          have := nd2 q hq hd hqn2
          subst this
          omega
        · intro hd; exact nd1' q hq hd hqn2
      obtain ⟨m, hpow2⟩ : ∃ m, n + 2 = 3 ^ m :=
        ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (by omega) (fun {q} hq hd =>
          uniq 2 3 q Nat.prime_three h3 (cond 3 Nat.prime_three h3) hq hd (cond q hq hd))⟩
      have := e889_cat1 b m (by rw [← hpow]; omega)
      interval_cases b <;> simp at hpow <;> omega
    · have h3 : 3 ∣ n + 1 := by omega
      rw [hpow] at h3
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow h3)
      omega

/--
$v_l(n)$ is the supremum of $v(n,k)$ for all $k \ge l$
-/
noncomputable def v_l (l n : ℕ) : ℕ∞ :=
  ⨆ k ≥ l, (v n k : ℕ∞)

/--
Let $v_l(n) = \max_{k\geq l} v(n,k)$. For every fixed $l$,
$v_l(n) \to \infty$ as $n \to \infty$

[ErSe67] Erdős, P. and Selfridge, J. L., Some problems on the prime factors of consecutive integers. Illinois J. Math. (1967), 428--430.
-/
@[category research open, AMS 11]
theorem erdos_889.variants.general :
    ∀ l, Tendsto (v_l l) atTop (𝓝 ⊤) := by
  sorry

/--
Does $v_1(n) = 1$ have finite solutions?

[ErSe67] Erdős, P. and Selfridge, J. L., Some problems on the prime factors of consecutive integers. Illinois J. Math. (1967), 428--430.
-/
@[category research open, AMS 11]
theorem erdos_889.variants.v1_eq_1_finite :
    answer(sorry) ↔ {n | v_l 1 n = 1}.Finite := by
  sorry

/--
$V(n,k)$ is the number of primes $p$ such that
$p^\alpha$ exactly divides $n+k$ and
for all $0 \le i < k$, $p^\alpha$ does not divide $n+i$,
where $\alpha$ is the multiplicity of $p$ in the factorization of $n+k$.
-/
def V (n k : ℕ) : ℕ :=
  ((n + k).primeFactors.filter (fun p =>
    ∀ i ∈ range k, ¬ p ^ ((n + k).factorization p) ∣ n + i)).card

/--
$V_l(n)$ is the supremum of $V(n,k)$ for all $k \ge l$
-/
noncomputable def V_l (l n : ℕ) : ℕ∞ :=
  ⨆ k ≥ l, (V n k : ℕ∞)

/--
Does $V_1(n) = 1$ have finite solutions?

This is a modification of `erdos_889.variants.v1_eq_1_finite`,
which might make it more amenable to attack according to [ErSe67].

[ErSe67] Erdős, P. and Selfridge, J. L., Some problems on the prime factors of consecutive integers. Illinois J. Math. (1967), 428--430.
-/
@[category research open, AMS 11]
theorem erdos_889.variants.V1_eq_1_finite :
    answer(sorry) ↔ {n | V_l 1 n = 1}.Finite := by
  sorry

end Erdos889
