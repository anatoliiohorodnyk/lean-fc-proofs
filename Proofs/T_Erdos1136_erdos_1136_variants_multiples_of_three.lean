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
# Erdős Problem 1136

*References:*
- [erdosproblems.com/1136](https://www.erdosproblems.com/1136)
- [Mu11] Müller, Helmut, *Über ein additiv-zahlentheoretisches Problem von P. Erdős*.
  Mitt. Math. Ges. Hamburg (2011), 75-78.
-/

@[expose] public section

namespace Erdos1136

/--
A set `A` of natural numbers has the property in the question if `a + b ≠ 2 ^ k` for all
`a, b ∈ A` (not necessarily distinct) and all `k ≥ 0`.
-/
def AvoidsPowersOfTwo (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ k : ℕ, a + b ≠ 2 ^ k

/-- The set of all integers congruent to $3\cdot 2^i\pmod{2^{i+2}}$ for some $i\geq 0$. -/
def muellerSet : Set ℕ := {n | ∃ i : ℕ, n ≡ 3 * 2 ^ i [MOD 2 ^ (i + 2)]}

/--
Does there exist $A\subset \mathbb{N}$ with lower density $>1/3$ such that $a+b\neq 2^k$ for
any $a,b\in A$ and $k\geq 0$?

Müller [Mu11] settled this question in the affirmative: in fact one can take $A$ to be
the set of all integers congruent to $3\cdot 2^i\pmod{2^{i+2}}$ for any $i\geq 0$, which has
density $1/2$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos1136.lean"]
theorem erdos_1136 : answer(True) ↔
    ∃ A : Set ℕ, (1 / 3 : ℝ) < A.lowerDensity ∧ AvoidsPowersOfTwo A := by
  sorry

lemma e1136_count (n : ℕ) : ((Finset.range n).filter (fun m => 3 ∣ m)).card = (n + 2) / 3 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp), ih]; omega
    · rw [ih]; omega

open Set in
lemma e1136_ncard (n : ℕ) : ({m : ℕ | 3 ∣ m} ∩ Iio n).ncard = (n + 2) / 3 := by
  rw [← e1136_count, ← Set.ncard_coe_finset]
  congr 1; ext m; simp [and_comm]

/--
Achieving density $1/3$ is trivial, taking $A$ to be all multiples of $3$.
-/
@[category research solved, AMS 11]
theorem erdos_1136.variants.multiples_of_three :
    AvoidsPowersOfTwo {n : ℕ | 3 ∣ n} ∧ Set.HasDensity {n : ℕ | 3 ∣ n} (1 / 3) := by
  refine ⟨?_, ?_⟩
  · intro a ha b hb k h
    have h3 : 3 ∣ 2 ^ k := h ▸ dvd_add ha hb
    have := (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) h3)
    omega
  · unfold Set.HasDensity Set.partialDensity
    have hval : ∀ n : ℕ, 1 ≤ n → ((({n : ℕ | 3 ∣ n} ∩ Set.univ) ∩ Set.Iio n).ncard : ℝ) / (Set.univ ∩ Set.Iio n).ncard
        = (((n + 2) / 3 : ℕ) : ℝ) / n := by
      intro n _
      rw [Set.inter_univ, Set.univ_inter, e1136_ncard, Nat.ncard_Iio]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (h := fun n : ℕ => 1 / 3 + 1 / (n : ℝ)) ?_ ?_ ?_
    · simpa using (tendsto_const_nhds (x := (1 / 3 : ℝ))).add tendsto_one_div_atTop_nhds_zero_nat
    · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      rw [hval n hn]
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have h1 : (n : ℝ) ≤ 3 * (((n + 2) / 3 : ℕ) : ℝ) := by
        have : n ≤ 3 * ((n + 2) / 3) := by omega
        exact_mod_cast this
      rw [le_div_iff₀ hn']; linarith
    · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      rw [hval n hn]
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have h1 : 3 * (((n + 2) / 3 : ℕ) : ℝ) ≤ n + 3 := by
        have : 3 * ((n + 2) / 3) ≤ n + 3 := by omega
        exact_mod_cast this
      rw [div_le_iff₀ hn', add_mul, div_mul_cancel₀ _ hn'.ne']; linarith

/--
Müller [Mu11] settled this question in the affirmative: in fact one can take $A$ to be
the set of all integers congruent to $3\cdot 2^i\pmod{2^{i+2}}$ for any $i\geq 0$, which has
density $1/2$.
-/
@[category research solved, AMS 11]
theorem erdos_1136.variants.mueller :
    AvoidsPowersOfTwo muellerSet ∧ muellerSet.HasDensity (1 / 2) := by
  sorry

/--
Müller also proved this is best possible, in that $A$ with the property in the question has
lower density at most $1/2$.
-/
@[category research solved, AMS 11]
theorem erdos_1136.variants.upper_bound (A : Set ℕ) (hA : AvoidsPowersOfTwo A) :
    A.lowerDensity ≤ 1 / 2 := by
  sorry

end Erdos1136
