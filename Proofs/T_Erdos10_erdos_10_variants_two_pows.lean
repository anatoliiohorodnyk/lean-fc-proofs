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
# Erdős Problem 10

*References:*
- [erdosproblems.com/10](https://www.erdosproblems.com/10)
- [Cr71] Crocker, R., On the sum of a prime and of two powers of two. Pacific J. Math. 36 (1971),
  103-107.
- [Ga75] Gallagher, P. X., Primes and powers of 2. Acta Arith. 29 (1976), 353-370.
- [GrSo98] Granville, A. and Soundararajan, K., A binary additive problem of Erdős and the
  order of $2$ mod $p^2$. Ramanujan J. 2 (1998), 283-298.
-/

@[expose] public section

open Filter

namespace Erdos10

/--
The set of natural numbers that can be written as a sum
of a prime and at most $k$ powers of $2$.
-/
abbrev sumPrimeAndTwoPows (k : ℕ) : Set ℕ :=
  { p + (pows.map (2 ^ ·)).sum | (p : ℕ) (pows : Multiset ℕ) (_ : p.Prime)
    (_ : pows.card ≤ k)}

/-- A prime is the sum of a prime and no powers of $2$. -/
@[category test, AMS 5 11]
theorem two_mem_sumPrimeAndTwoPows_zero : 2 ∈ sumPrimeAndTwoPows 0 :=
  ⟨2, 0, Nat.prime_two, by simp, by simp⟩

/-- $1$ is smaller than every prime, so it lies in no `sumPrimeAndTwoPows k`. -/
@[category test, AMS 5 11]
theorem one_not_mem_sumPrimeAndTwoPows (k : ℕ) : 1 ∉ sumPrimeAndTwoPows k := by
  rintro ⟨p, pows, hp, -, h⟩
  have : 2 ≤ p := hp.two_le
  omega

/--
Is there some $k$ such that every large integer is the sum of a prime and at most $k$
powers of $2$?
-/
@[category research open, AMS 5 11]
theorem erdos_10 : answer(sorry) ↔ ∃ k, ∀ᶠ n : ℕ in atTop, n ∈ sumPrimeAndTwoPows k := by
  sorry

/--
Gallagher [Ga75] has shown that for any $ϵ > 0$ there exists $k(ϵ)$
such that the set of integers which are the sum of a prime and at most $k(ϵ)$
many powers of $2$ has lower density at least $1 - ϵ$.

Ref: Gallagher, P. X., _Primes and powers of 2_.
-/
@[category research solved, AMS 5 11]
theorem erdos_10.variants.gallagher (ε : ℝ)
    (hε : 0 < ε) : ∃ k, 1 - ε ≤ (sumPrimeAndTwoPows k).lowerDensity := by
  sorry

/--
Granville and Soundararajan [GrSo98] have conjectured that at most $3$
powers of $2$ suffice for all odd integers, and hence at most $4$ powers of $2$
suffice for all even integers.

Ref: Granville, A. and Soundararajan, K., _A Binary Additive Problem of Erdős and the Order of $2$ mod $p^2$_
-/
@[category research open, AMS 5 11]
theorem erdos_10.variants.granville_soundararajan_odd :
    {n : ℕ | Odd n ∧ 1 < n} ⊆ sumPrimeAndTwoPows 3 ∧
      {n : ℕ | Even n ∧ n ≠ 0} ⊆ sumPrimeAndTwoPows 4 := by
  sorry

/--
Bogdan Grechuk has observed that `1117175146` is not the sum of a prime
and at most $3$ powers of $2$.
-/
@[category research solved, AMS 5 11]
theorem erdos_10.variants.grechuk_example :
    1117175146 ∉ sumPrimeAndTwoPows 3 := by
  sorry

lemma e16_pow (q k : ℕ) (h : 2 ^ 24 % q = 1) : 2 ^ k % q = 2 ^ (k % 24) % q := by
  conv_lhs => rw [← Nat.div_add_mod k 24, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod, h]
  simp

lemma e16_pow31 (k : ℕ) : 2 ^ k % 31 = 1 ∨ 2 ^ k % 31 = 2 ∨ 2 ^ k % 31 = 4 ∨ 2 ^ k % 31 = 8 ∨
    2 ^ k % 31 = 16 := by
  have : 2 ^ k % 31 = 2 ^ (k % 5) % 31 := by
    conv_lhs => rw [← Nat.div_add_mod k 5, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  rw [this]
  have : k % 5 < 5 := Nat.mod_lt _ (by norm_num)
  interval_cases (k % 5) <;> simp

lemma e10_cov (m k p : ℕ) (hp : p.Prime) (hx : 119477317 + m * 346729110 = 2 ^ k + p) : False := by
  have h31 := e16_pow31 k
  have hr : k % 24 < 24 := Nat.mod_lt _ (by norm_num)
  generalize hr' : k % 24 = r at hr
  interval_cases r
  · have hX := e16_pow 3 k (by norm_num)
    rw [hr'] at hX; norm_num at hX
    generalize 2 ^ k = X at hX h31 hx
    have hpq : 3 ∣ p := by omega
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp hpq
    subst this
    omega
  · have hX := e16_pow 5 k (by norm_num)
    rw [hr'] at hX; norm_num at hX
    generalize 2 ^ k = X at hX h31 hx
    have hpq : 5 ∣ p := by omega
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp hpq
    subst this
    omega
  · have hX := e16_pow 3 k (by norm_num)
    rw [hr'] at hX; norm_num at hX
    generalize 2 ^ k = X at hX h31 hx
    have hpq : 3 ∣ p := by omega
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp hpq
    subst this
    omega
  · have hX := e16_pow 17 k (by norm_num)
    rw [hr'] at hX; norm_num at hX
    generalize 2 ^ k = X at hX h31 hx
    have hpq : 17 ∣ p := by omega
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp hpq
    subst this
    omega
  · have hX := e16_pow 3 k (by norm_num)
    rw [hr'] at hX; norm_num at hX
    generalize 2 ^ k = X at hX h31 hx
    have hpq : 3 ∣ p := by omega
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp hpq
    subst this
    omega
  · have hX := e16_pow 5 k (by norm_num)
    rw [hr'] at hX; norm_num at hX
    generalize 2 ^ k = X at hX h31 hx
    have hpq : 5 ∣ p := by omega
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp hpq
    subst this
    omega
  · have hX := e16_pow 3 k (by norm_num)
    rw [hr'] at hX; norm_num at hX
    generalize 2 ^ k = X at hX h31 hx
    have hpq : 3 ∣ p := by omega
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp hpq
    subst this
    omega
  · have hX := e16_pow 13 k (by norm_num)
    rw [hr'] at hX; norm_num at hX
    generalize 2 ^ k = X at hX h31 hx
    have hpq : 13 ∣ p := by omega
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp hpq
    subst this
    omega
  · have hX := e16_pow 3 k (by norm_num)
    rw [hr'] at hX; norm_num at hX
    generalize 2 ^ k = X at hX h31 hx
    have hpq : 3 ∣ p := by omega
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp hpq
    subst this
    omega
  · have hX := e16_pow 5 k (by norm_num)
    rw [hr'] at hX; norm_num at hX
    generalize 2 ^ k = X at hX h31 hx
    have hpq : 5 ∣ p := by omega
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp hpq
    subst this
    omega
  · have hX := e16_pow 3 k (by norm_num)
    rw [hr'] at hX; norm_num at hX
    generalize 2 ^ k = X at hX h31 hx
    have hpq : 3 ∣ p := by omega
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp hpq
    subst this
    omega
  · have hX := e16_pow 17 k (by norm_num)
    rw [hr'] at hX; norm_num at hX
    generalize 2 ^ k = X at hX h31 hx
    have hpq : 17 ∣ p := by omega
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp hpq
    subst this
    omega
  · have hX := e16_pow 3 k (by norm_num)
    rw [hr'] at hX; norm_num at hX
    generalize 2 ^ k = X at hX h31 hx
    have hpq : 3 ∣ p := by omega
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp hpq
    subst this
    omega
  · have hX := e16_pow 5 k (by norm_num)
    rw [hr'] at hX; norm_num at hX
    generalize 2 ^ k = X at hX h31 hx
    have hpq : 5 ∣ p := by omega
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp hpq
    subst this
    omega
  · have hX := e16_pow 3 k (by norm_num)
    rw [hr'] at hX; norm_num at hX
    generalize 2 ^ k = X at hX h31 hx
    have hpq : 3 ∣ p := by omega
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp hpq
    subst this
    omega
  · have hX := e16_pow 7 k (by norm_num)
    rw [hr'] at hX; norm_num at hX
    generalize 2 ^ k = X at hX h31 hx
    have hpq : 7 ∣ p := by omega
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp hpq
    subst this
    omega
  · have hX := e16_pow 3 k (by norm_num)
    rw [hr'] at hX; norm_num at hX
    generalize 2 ^ k = X at hX h31 hx
    have hpq : 3 ∣ p := by omega
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp hpq
    subst this
    omega
  · have hX := e16_pow 5 k (by norm_num)
    rw [hr'] at hX; norm_num at hX
    generalize 2 ^ k = X at hX h31 hx
    have hpq : 5 ∣ p := by omega
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp hpq
    subst this
    omega
  · have hX := e16_pow 3 k (by norm_num)
    rw [hr'] at hX; norm_num at hX
    generalize 2 ^ k = X at hX h31 hx
    have hpq : 3 ∣ p := by omega
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp hpq
    subst this
    omega
  · have hX := e16_pow 17 k (by norm_num)
    rw [hr'] at hX; norm_num at hX
    generalize 2 ^ k = X at hX h31 hx
    have hpq : 17 ∣ p := by omega
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp hpq
    subst this
    omega
  · have hX := e16_pow 3 k (by norm_num)
    rw [hr'] at hX; norm_num at hX
    generalize 2 ^ k = X at hX h31 hx
    have hpq : 3 ∣ p := by omega
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp hpq
    subst this
    omega
  · have hX := e16_pow 5 k (by norm_num)
    rw [hr'] at hX; norm_num at hX
    generalize 2 ^ k = X at hX h31 hx
    have hpq : 5 ∣ p := by omega
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp hpq
    subst this
    omega
  · have hX := e16_pow 3 k (by norm_num)
    rw [hr'] at hX; norm_num at hX
    generalize 2 ^ k = X at hX h31 hx
    have hpq : 3 ∣ p := by omega
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp hpq
    subst this
    omega
  · have hX := e16_pow 241 k (by norm_num)
    rw [hr'] at hX; norm_num at hX
    generalize 2 ^ k = X at hX h31 hx
    have hpq : 241 ∣ p := by omega
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp hpq
    subst this
    omega

lemma e10_mem (m : ℕ) :
    119477317 + m * 346729110 + 1 ∈ {n : ℕ | Even n} \ sumPrimeAndTwoPows 2 := by
  refine ⟨Nat.even_iff.mpr (by omega), ?_⟩
  rintro ⟨p, pows, hp, hcard, heq⟩
  have hb31 := e16_pow31
  rcases Nat.lt_or_ge pows.card 2 with hlt | hge
  · rcases Nat.lt_or_ge pows.card 1 with hlt1 | hge1
    · rw [Multiset.card_eq_zero.mp (show pows.card = 0 by omega)] at heq
      simp at heq
      rcases hp.eq_two_or_odd with h2 | h2 <;> omega
    · obtain ⟨b, rfl⟩ := Multiset.card_eq_one.mp (show pows.card = 1 by omega)
      simp at heq
      rcases Nat.eq_zero_or_pos b with hb | hb
      · subst hb
        simp at heq
        have h31 : 31 ∣ p := by omega
        have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp h31
        omega
      · have h2b : 2 ∣ 2 ^ b := dvd_pow_self 2 (by omega)
        have hb' := hb31 b
        rcases hp.eq_two_or_odd with h2 | h2
        · subst h2
          generalize 2 ^ b = X at h2b hb' heq
          omega
        · generalize 2 ^ b = X at h2b hb' heq
          omega
  · obtain ⟨b, c, rfl⟩ := Multiset.card_eq_two.mp (show pows.card = 2 by omega)
    simp at heq
    have hb' := hb31 b
    have hc' := hb31 c
    rcases hp.eq_two_or_odd with h2 | h2
    · subst h2
      generalize 2 ^ b = X at hb' heq
      generalize 2 ^ c = Y at hc' heq
      omega
    · rcases Nat.eq_zero_or_pos b with hb | hb <;> rcases Nat.eq_zero_or_pos c with hc | hc
      · subst hb; subst hc; simp at heq; omega
      · subst hb
        simp at heq
        exact e10_cov m c p hp (by omega)
      · subst hc
        simp at heq
        exact e10_cov m b p hp (by omega)
      · have h2b : 2 ∣ 2 ^ b := dvd_pow_self 2 (by omega)
        have h2c : 2 ∣ 2 ^ c := dvd_pow_self 2 (by omega)
        generalize 2 ^ b = X at h2b heq
        generalize 2 ^ c = Y at h2c heq
        omega

/--
There are infinitely many even integers not the sum of a prime and $2$ powers of $2$
-/
@[category research solved, AMS 5 11]
theorem erdos_10.variants.two_pows :
    Set.Infinite <| {n : ℕ | Even n} \ sumPrimeAndTwoPows 2 := by
  refine Set.infinite_of_injective_forall_mem (f := fun m : ℕ => 119477317 + m * 346729110 + 1)
    (fun x y h => by simp at h; omega) e10_mem

/--
Bogdan Grechuk has observed that $1117175146$ is not the sum of a prime and at most $3$
powers of $2$, and pointed out that parity considerations, coupled with the fact that there
are many integers not the sum of a prime and $2$ powers of $2$ suggest that there exist
infinitely many even integers which are not the sum of a prime and at most $3$ powers of $2$.

This follows from Crocker's construction [Cr71] of infinitely many odd $t \equiv 15 \pmod{16}$
which are not the sum of a prime and $2$ powers of $2$: each such $t + 1$ is even and not the
sum of a prime and at most $3$ powers of $2$.

The linked Lean formalisation is by Daryxx, see comment section.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://gist.github.com/DaryxXx/e112c74cc648b08a420b0959315cf65f/4b347897ff1811f1db1d82594c581f54b8f31b7d#file-main-lean-L2287"]
theorem erdos_10.variants.grechuk :
    Set.Infinite <| {n : ℕ | Even n} \ sumPrimeAndTwoPows 3 := by
  sorry

end Erdos10
