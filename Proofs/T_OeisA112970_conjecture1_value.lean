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
# A generalized Stern sequence

A112970: A generalized Stern sequence, defined by the recurrence relations:
$a(2n+1) = a(n)$ and $a(2n) = a(n) + a(n-2)$ with $a(0)=1$, $a(1)=1$ and $a(n)=0$ for $n \le -1$.

*References:*
- [A112970](https://oeis.org/A112970)
-/

@[expose] public section

namespace OeisA112970

/--
a n is the generalized Stern sequence, defined by the recurrence relations:
$a(2n+1) = a(n)$ and $a(2n) = a(n)$ + $a(n-2)$ with $a(0) = 1$, $a(1) = 1$
and $a(n) = 0$ for $n \le -1$.
-/
def a (n : ℕ) : ℕ :=
  if n = 0 then 1
  else if n = 1 then 1
  else
    let k := n / 2
    if n % 2 = 1 then -- Odd case: a(2k + 1) = a(k)
      a k
    else -- Even case: a(2k) = a(k) + a(k - 2)
      let aPrev : ℕ :=
        -- a(m) is 0 if m < 0. Equivalent to checking k < 2 for the argument k-2.
        if k < 2 then 0
        else a (k - 2)
      a k + aPrev
termination_by n

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by unfold a; rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by unfold a; rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by unfold a; unfold a; unfold a; rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by unfold a; unfold a; rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 2 := by unfold a; unfold a; unfold a; unfold a; rfl

/--
Conjecture: $a(2^n)=a(2^(n+1)+1)=\textrm{A033638}(n)$.
This formalizes the equality $a(2^n) = a(2^(n+1)+1)$.
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/oeis-a112970-formal-conjectures/blob/71ae72f443bd9bee7d958f0a19d9f9ec5ab82af5/lean/OeisA112970FC.lean#L43-L46"]
theorem conjecture1 (n : ℕ) : a (2^n) = a (2^(n + 1) + 1) := by
  sorry

lemma st_odd (k : ℕ) : a (2 * k + 1) = a k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [a_0]; exact a_1
  · rw [a]
    have h1 : (2 * k + 1) / 2 = k := by omega
    simp only [show 2 * k + 1 ≠ 0 by omega, show 2 * k + 1 ≠ 1 by omega, if_false, h1,
      show (2 * k + 1) % 2 = 1 by omega, if_true]

lemma st_even (k : ℕ) (hk : 2 ≤ k) : a (2 * k) = a k + a (k - 2) := by
  rw [a]
  have h1 : (2 * k) / 2 = k := by omega
  simp only [show 2 * k ≠ 0 by omega, show 2 * k ≠ 1 by omega, if_false, h1,
    show (2 * k) % 2 = 0 by omega, show ¬ (k < 2) by omega]
  simp

lemma st_two : a 2 = 1 := by
  rw [a]; simp [a_1]

lemma st_pow_sub_one (m : ℕ) : a (2 ^ m - 1) = 1 := by
  induction m with
  | zero => simpa using a_0
  | succ m ih =>
    have : 2 ^ (m + 1) - 1 = 2 * (2 ^ m - 1) + 1 := by
      have := Nat.one_le_two_pow (n := m); rw [pow_succ]; omega
    rw [this, st_odd, ih]

lemma st_pow_sub_two (m : ℕ) (hm : 1 ≤ m) : a (2 ^ m - 2) = (m + 1) / 2 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.lt_or_ge m 3 with h | h
    · interval_cases m
      · simpa using a_0
      · simpa using st_two
    · obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
      have hp : 2 ≤ 2 ^ j := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
      have e : 2 ^ (j + 2) - 2 = 2 * (2 ^ (j + 1) - 1) := by
        rw [pow_succ, pow_succ]; omega
      have e2 : 2 ^ (j + 1) - 1 - 2 = 2 * (2 ^ j - 2) + 1 := by
        rw [pow_succ]; omega
      rw [e, st_even _ (by rw [pow_succ]; omega), st_pow_sub_one, e2, st_odd,
        ih j (by omega) (by omega)]
      omega

lemma st_sq_div (n : ℕ) : (n + 1) ^ 2 / 4 = n ^ 2 / 4 + (n + 1) / 2 := by
  rcases Nat.even_or_odd' n with ⟨t, rfl | rfl⟩
  · have h1 : (2 * t + 1) ^ 2 = 4 * (t * t + t) + 1 := by ring
    have h2 : (2 * t) ^ 2 = 4 * (t * t) := by ring
    rw [h1, h2]; generalize t * t = s; omega
  · have h1 : (2 * t + 1 + 1) ^ 2 = 4 * (t * t + 2 * t + 1) := by ring
    have h2 : (2 * t + 1) ^ 2 = 4 * (t * t + t) + 1 := by ring
    rw [h1, h2]; generalize t * t = s; omega

/--
Second part of the conjecture, $a(2^n)=\textrm{A033638}(n)=\lfloor n^2 / 4 \rfloor + 1$.
It holds by induction on $n$, since $a(2^{n+1}) = a(2^n) + a(2^n - 2)$ for $n \ge 1$ and
$a(2^m - 2) = \lfloor (m+1)/2 \rfloor$ for $m \ge 1$.
-/
@[category research solved, AMS 11]
theorem conjecture1_value (n : ℕ) : a (2^n) = n ^ 2 / 4 + 1 := by
  induction n with
  | zero => simpa using a_1
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using st_two
    · have hp : 2 ≤ 2 ^ n := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      rw [pow_succ, mul_comm, st_even _ hp, ih, st_pow_sub_two n hn, st_sq_div]
      omega

/--
Conjecture: $a(2^n-1)=a(3*2^n-1)=1$.
This formalizes the equality part $a(2^n-1) = a(3*2^n-1)$.
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/oeis-a112970-formal-conjectures/blob/71ae72f443bd9bee7d958f0a19d9f9ec5ab82af5/lean/OeisA112970FC.lean#L56-L64"]
theorem conjecture2 (n : ℕ) : a (2^n - 1) = a (3 * 2^n - 1) := by
  sorry

/-- Conjecture: $a(2^n-1)=a(3*2^n-1)=1$. This formalizes the value part $a(2^n-1)=1$. -/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/oeis-a112970-formal-conjectures/blob/71ae72f443bd9bee7d958f0a19d9f9ec5ab82af5/lean/OeisA112970FC.lean#L48-L54"]
theorem conjecture3 (n : ℕ) : a (2^n - 1) = 1 := by
  sorry

end OeisA112970
