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
# Smallest power with base>1 and exponent $n$ without digit 0

For statistical reasons it is conjectured that the sequence is finite.
Also it is conjectured that $a(40)$ does not exist (i.e. the sequence is empty for $n=40$).

*References:*
- [A103662](https://oeis.org/A103662)
-/

@[expose] public section

namespace OeisA103662

open Nat List Set

/--
A helper predicate: $b^n$ is a power with base $>1$ whose decimal representation
does not contain the digit 0.
We assume $n$ is the exponent, $n \ge 1$.
-/
def IsValidZerolessPower (n b : ℕ) : Prop :=
  b > 1 ∧ 0 ∉ digits 10 (b ^ n)

/--
The primary defining sequence `a`.
`a n` is the smallest power with base $>1$ and exponent $n$ whose decimal representation
doesn't contain the digit 0.
$$a(n) = (\min \{ b \in \mathbb{N} \mid b > 1,
  \text{decimal representation of } b^n \text{ contains no digit } 0 \})^n$$
If no such base exists, `sInf` of an empty set of naturals returns 0, so `a n = 0`.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let smallestBase := sInf { b | IsValidZerolessPower n b }
  smallestBase ^ n

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by
  constructor

@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by
  simp_all[a]
  norm_num[Iff,IsValidZerolessPower]
  exact ( IsLeast.csInf_eq ⟨.symm (by norm_num), fun and => And.left⟩)

@[category test, AMS 11]
theorem a_2 : a 2 = 4 := by
  norm_num[a]
  delta IsValidZerolessPower
  exact (congr_arg) (.^2) (IsLeast.csInf_eq ⟨.symm (by norm_num), fun and=>And.left⟩)

@[category test, AMS 11]
theorem a_3 : a 3 = 8 := by
  norm_num[a]
  delta IsValidZerolessPower
  exact (.trans (by
    rw [IsLeast.csInf_eq (by use ⟨by constructor, by norm_num⟩, fun and' => And.left)])
    (by constructor))

lemma o103_digit (N j : ℕ) (hN : 10 ^ (j + 1) ≤ N) (hd : N / 10 ^ j % 10 = 0) : 0 ∈ digits 10 N := by
  have hlen : j < (digits 10 N).length := by
    by_contra h
    push Not at h
    have := (Nat.digits_length_le_iff (by norm_num) N).mp h
    have : 10 ^ j < 10 ^ (j + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hget := Nat.getD_digits N j (b := 10) (by norm_num)
  rw [hd, List.getD_eq_getElem _ _ hlen] at hget
  rw [← hget]
  exact List.getElem_mem hlen

lemma o103_odd16 (b : ℕ) (hb : b % 2 = 1) : b ^ 2500 % 16 = 1 := by
  have h4 : b ^ 4 % 16 = 1 := by
    have : b % 16 = 1 ∨ b % 16 = 3 ∨ b % 16 = 5 ∨ b % 16 = 7 ∨ b % 16 = 9 ∨ b % 16 = 11 ∨
        b % 16 = 13 ∨ b % 16 = 15 := by omega
    rw [Nat.pow_mod]
    rcases this with h | h | h | h | h | h | h | h <;> rw [h]
  rw [show 2500 = 4 * 625 by norm_num, pow_mul, Nat.pow_mod, h4, one_pow]; norm_num

lemma o103_euler (b : ℕ) (hb : ¬ 5 ∣ b) : b ^ 2500 % 3125 = 1 := by
  have hcop : Nat.Coprime b 3125 := by
    rw [show 3125 = 5 ^ 5 by norm_num]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hb)))
  have htot : Nat.totient 3125 = 2500 := by
    rw [show 3125 = 5 ^ 5 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]; norm_num
  have := Nat.ModEq.pow_totient hcop
  rw [htot] at this
  exact this

lemma o103_big (b : ℕ) (hb : 1 < b) : 10 ^ 5 ≤ b ^ 2500 := by
  calc 10 ^ 5 ≤ 2 ^ 17 := by norm_num
    _ ≤ 2 ^ 2500 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    _ ≤ b ^ 2500 := Nat.pow_le_pow_left hb _

lemma o103_zero (b : ℕ) (hb : 1 < b) : 0 ∈ digits 10 (b ^ 2500) := by
  set N := b ^ 2500 with hN
  have hbig := o103_big b hb
  by_cases h2 : b % 2 = 0
  · by_cases h5 : 5 ∣ b
    · -- `10 ∣ b`
      apply o103_digit N 0 (by omega)
      have : 10 ∣ N := by
        rw [hN]; exact Dvd.dvd.pow (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num)
          (Nat.dvd_of_mod_eq_zero h2) h5) (by norm_num)
      simp; omega
    · have h32 : N % 32 = 0 := by
        have : 32 ∣ N := by
          rw [hN, show (32 : ℕ) = 2 ^ 5 by norm_num]
          exact (pow_dvd_pow_of_dvd (Nat.dvd_of_mod_eq_zero h2) 5).trans
            (Nat.pow_dvd_pow b (by norm_num))
        omega
      have he := o103_euler b h5
      apply o103_digit N 4 (by omega)
      omega
  · have h16 := o103_odd16 b (by omega)
    by_cases h5 : 5 ∣ b
    · have h625 : N % 625 = 0 := by
        have : 625 ∣ N := by
          rw [hN, show (625 : ℕ) = 5 ^ 4 by norm_num]
          exact (pow_dvd_pow_of_dvd h5 4).trans (Nat.pow_dvd_pow b (by norm_num))
        omega
      apply o103_digit N 3 (by omega)
      omega
    · have he := o103_euler b h5
      apply o103_digit N 1 (by omega)
      omega

theorem o103_main : ∃ n : ℕ, a n = 0 := by
  refine ⟨2500, ?_⟩
  have hempty : { b | IsValidZerolessPower 2500 b } = ∅ := by
    ext b
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, IsValidZerolessPower, not_and,
      not_not]
    exact o103_zero b
  simp only [a, hempty, Nat.sInf_empty]
  norm_num

/--
For statistical reasons it is conjectured that the sequence is finite.
Finite means here that for some $n$, no power $b^n$ with base $b > 1$ has a zeroless decimal
representation, which in our definition results in $a(n) = 0$.

This holds for $n = 2500$
([source](https://tadamcz.com/fc-review-results/aea251bb26/#/f/OEIS/103662)).
Take any integer $b > 1$ and let $N = b^{2500}$. Since $b \ge 2$, we have
$N \ge 2^{2500} > 10^5$, so $N$ has at least six decimal digits. We split into four cases
depending on the divisibility of $b$ by $2$ and $5$:

- **If $10 \mid b$:** Then $10 \mid N$, so the units digit of $N$ is $0$.
- **If $b$ is odd and $5 \nmid b$:** Since $b$ is odd and the Carmichael function satisfies
  $\lambda(16) = 4 \mid 2500$, we have $N \equiv 1 \pmod{16}$. Since $5 \nmid b$ and
  $\varphi(5^5) = 2500$, Euler's totient theorem gives $N \equiv 1 \pmod{3125}$. By the Chinese
  Remainder Theorem, $N \equiv 1 \pmod{50000}$ (as $16 \cdot 3125 = 50000$), so the tens digit
  of $N$ is $0$.
- **If $b$ is odd and $5 \mid b$:** As above, $N \equiv 1 \pmod{16}$. Since $5 \mid b$ and
  $2500 \ge 4$, we also have $5^4 = 625 \mid N$, so $N \equiv 0 \pmod{625}$. Since
  $16 \cdot 625 = 10^4$ and $625 \equiv 1 \pmod{16}$, the Chinese Remainder Theorem gives
  $N \equiv 625 \pmod{10^4}$. Because $N > 10^4$, the last four digits of $N$ are $0625$, so its
  thousands digit is $0$.
- **If $b$ is even and $5 \nmid b$:** Since $2 \mid b$ and $2500 \ge 5$, we have
  $2^5 = 32 \mid N$, so $N \equiv 0 \pmod{32}$. Since $5 \nmid b$, Euler's theorem again gives
  $N \equiv 1 \pmod{3125}$. Because $32 \cdot 3125 = 10^5$ and
  $9376 = 293 \cdot 32 = 3 \cdot 3125 + 1$, the Chinese Remainder Theorem gives
  $N \equiv 9376 \pmod{10^5}$. Since $N > 10^5$, the last five digits of $N$ are $09376$, so its
  ten-thousands digit is $0$.

In every case, the decimal representation of $N$ contains the digit $0$, so $a(2500) = 0$.
-/
@[category research solved, AMS 11]
theorem conjecture : ∃ n : ℕ, a n = 0 := by
  exact o103_main

/--
$a(40)$, if it exists, is not known.

This claim is rooted in the finiteness conjecture. The most direct mathematical expression
of the open problem concerning $a(40)$ is the negation of the existence of a valid base.
-/
@[category research open, AMS 11]
theorem conjecture.variants.a_40 :
  ¬ ∃ (b : ℕ), IsValidZerolessPower 40 b := by
  sorry

end OeisA103662
