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
# Erdős Problem 1148

*References:*
- [erdosproblems.com/1148](https://www.erdosproblems.com/1148)
- [Ch26] P. Chojecki, [Bounded Representations by $x^2 + y^2 - z^2$](https://www.ulam.ai/research/erdos1148-full.pdf) (2026)
- [Va99] Various, Some of Paul's favorite problems. Booklet produced for the conference "Paul Erdős
  and his mathematics", Budapest, July 1999 (1999).
-/

@[expose] public section

open Filter

namespace Erdos1148

/--
A natural number $n$ which can be written as $n$ if $n = x^2 + y^2 - z^2$ with $\max(x^2, y^2, z^2)
\leq n$.
-/
def Erdos1148Prop (n : ℕ) : Prop :=
  ∃ x y z : ℕ, n = x ^ 2 + y ^ 2 - z ^ 2 ∧ x ^ 2 ≤ n ∧ y ^ 2 ≤ n ∧ z ^ 2 ≤ n

/--
Can every large integer $n$ be written as $n=x^2+y^2-z^2$ with $\max(x^2,y^2,z^2)\leq n$?

This was proved affirmatively by Chojecki [Ch26], using a Duke-type equidistribution theorem.
A Lean formalisation of the reduction (conditional on a Duke-type equidistribution theorem) exists;
see the [forum discussion](https://www.erdosproblems.com/forum/thread/1148#post-4849). The linked
formal proof (plby/lean-proofs) removes the Duke hypothesis; it is stated over `ℤ`, as
`∃ N, ∀ n ≥ N, ∃ x y z : ℤ, n = x ^ 2 + y ^ 2 - z ^ 2 ∧ max (x ^ 2) (max (y ^ 2) (z ^ 2)) ≤ n`,
which gives the statement below by taking absolute values.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1148.lean#L238"]
theorem erdos_1148 : answer(True) ↔ ∀ᶠ n in atTop, Erdos1148Prop n := by
  sorry

/--
The largest integer known which cannot be written this way is $6563$.
-/
private instance (n : ℕ) : Decidable (Erdos1148Prop n) :=
  decidable_of_iff
    (∃ x ∈ Finset.range (Nat.sqrt n + 1), ∃ y ∈ Finset.range (Nat.sqrt n + 1),
      ∃ z ∈ Finset.range (Nat.sqrt n + 1),
      n = x ^ 2 + y ^ 2 - z ^ 2 ∧ x ^ 2 ≤ n ∧ y ^ 2 ≤ n ∧ z ^ 2 ≤ n)
    (by
      constructor
      · rintro ⟨x, -, y, -, z, -, h⟩; exact ⟨x, y, z, h⟩
      · rintro ⟨x, y, z, h1, h2, h3, h4⟩
        refine ⟨x, Finset.mem_range.mpr ?_, y, Finset.mem_range.mpr ?_,
                z, Finset.mem_range.mpr ?_, h1, h2, h3, h4⟩
        all_goals (simp only [Nat.lt_succ_iff]; exact Nat.le_sqrt'.mpr ‹_›))

/--
The integer $6563$ cannot be written as $x^2 + y^2 - z^2$ with $\max(x^2, y^2, z^2) \leq 6563$.
-/
@[category textbook, AMS 11]
theorem erdos_1148.variants.lower_bound : ¬ Erdos1148Prop 6563 := by
  decide +native

/--
The weaker property: $n = x^2 + y^2 - z^2$ such that $\max(x^2, y^2, z^2) \leq n + 2\sqrt{n}$.
-/
def erdos_1148_weaker_prop (n : ℕ) : Prop :=
  ∃ x y z : ℕ, n = x ^ 2 + y ^ 2 - z ^ 2 ∧
    (x ^ 2 : ℝ) ≤ n + 2 * Real.sqrt n ∧
    (y ^ 2 : ℝ) ≤ n + 2 * Real.sqrt n ∧
    (z ^ 2 : ℝ) ≤ n + 2 * Real.sqrt n

lemma e1148_of (n x y z : ℕ) (h : x ^ 2 + y ^ 2 = n + z ^ 2) (hx : x ^ 2 ≤ n + 2 * Nat.sqrt n)
    (hy : y ^ 2 ≤ n + 2 * Nat.sqrt n) (hz : z ^ 2 ≤ n + 2 * Nat.sqrt n) :
    erdos_1148_weaker_prop n := by
  have hs : ((Nat.sqrt n : ℕ) : ℝ) ≤ Real.sqrt n := Real.nat_sqrt_le_real_sqrt
  refine ⟨x, y, z, by omega, ?_, ?_, ?_⟩
  · have : ((x ^ 2 : ℕ) : ℝ) ≤ ((n + 2 * Nat.sqrt n : ℕ) : ℝ) := by exact_mod_cast hx
    push_cast at this; linarith
  · have : ((y ^ 2 : ℕ) : ℝ) ≤ ((n + 2 * Nat.sqrt n : ℕ) : ℝ) := by exact_mod_cast hy
    push_cast at this; linarith
  · have : ((z ^ 2 : ℕ) : ℝ) ≤ ((n + 2 * Nat.sqrt n : ℕ) : ℝ) := by exact_mod_cast hz
    push_cast at this; linarith

/--
[Va99] reports this is 'obvious' if we replace $\leq n$ with $\leq n+2\sqrt{n}$.
-/
@[category research solved, AMS 11]
theorem erdos_1148.variants.weaker : ∀ n, erdos_1148_weaker_prop n := by
  intro n
  set s := Nat.sqrt n with hsdef
  have hs1 : s * s ≤ n := Nat.sqrt_le n
  have hs2 : n < (s + 1) * (s + 1) := Nat.lt_succ_sqrt n
  obtain ⟨u, hu⟩ : ∃ u, n = s * s + u := ⟨n - s * s, by omega⟩
  have hu2 : u ≤ 2 * s := by nlinarith
  rcases Nat.eq_zero_or_pos u with h0 | hpos
  · exact e1148_of n s 0 0 (by rw [hu, h0]; ring) (by nlinarith) (by simp) (by simp)
  · -- t = 2s + 1 - u
    have ht : ∃ t, t + u = 2 * s + 1 ∧ 1 ≤ t := ⟨2 * s + 1 - u, by omega, by omega⟩
    obtain ⟨t, htu, ht1⟩ := ht
    have hmod : t % 4 = 1 ∨ t % 4 = 3 ∨ t % 4 = 0 ∨ t % 4 = 2 := by omega
    rcases hmod with h | h | h | h
    · obtain ⟨k, rfl⟩ : ∃ k, t = 2 * k + 1 := ⟨t / 2, by omega⟩
      have hk : k + 1 ≤ s := by omega
      exact e1148_of n (s + 1) k (k + 1) (by rw [hu]; nlinarith) (by nlinarith) (by nlinarith)
        (by nlinarith)
    · obtain ⟨k, rfl⟩ : ∃ k, t = 2 * k + 1 := ⟨t / 2, by omega⟩
      have hk : k + 1 ≤ s := by omega
      exact e1148_of n (s + 1) k (k + 1) (by rw [hu]; nlinarith) (by nlinarith) (by nlinarith)
        (by nlinarith)
    · obtain ⟨k, rfl⟩ : ∃ k, t = 4 * k + 4 := ⟨t / 4 - 1, by omega⟩
      have hk : k + 2 ≤ s := by omega
      exact e1148_of n (s + 1) k (k + 2) (by rw [hu]; nlinarith) (by nlinarith) (by nlinarith)
        (by nlinarith)
    · obtain ⟨j, hj⟩ : ∃ j, u = 2 * j + 1 := ⟨u / 2, by omega⟩
      have hj' : j + 1 ≤ s := by omega
      exact e1148_of n s (j + 1) j (by rw [hu, hj]; ring) (by nlinarith) (by nlinarith)
        (by nlinarith)

end Erdos1148
