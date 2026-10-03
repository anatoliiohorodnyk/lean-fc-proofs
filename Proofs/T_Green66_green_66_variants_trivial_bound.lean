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
# Ben Green's Open Problem 66

*Reference:* [Ben Green's Open Problem 66](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#section.8)
-/

@[expose] public section

open Filter

namespace Green66

/-- A natural number is a sum of two squares if it can be written as `a ^ 2 + b ^ 2`. -/
def IsSumOfTwoSquares (n : ℕ) : Prop :=
  ∃ a b : ℕ, n = a ^ 2 + b ^ 2

/--
Is there always a sum of two squares between $X - \frac{1}{10}X^{1/4}$ and $X$?
We formalize this as an eventual statement for sufficiently large real $X$.
-/
@[category research open, AMS 11]
theorem green_66 :
    answer(sorry) ↔
      ∀ᶠ X : ℝ in atTop,
        ∃ n : ℕ, IsSumOfTwoSquares n ∧
          (n : ℝ) ∈ Set.Icc (X - (1 / 10 : ℝ) * X ^ (1 / 4 : ℝ)) X := by
  sorry

/--
Green notes that a well-known, almost trivial argument gives an $O(X^{1/4})$ bound on the left.
-/
@[category research solved, AMS 11]
theorem green_66.variants.trivial_bound :
    ∃ C > (0 : ℝ), ∀ᶠ X : ℝ in atTop,
      ∃ n : ℕ, IsSumOfTwoSquares n ∧
        (n : ℝ) ∈ Set.Icc (X - C * X ^ (1 / 4 : ℝ)) X := by
  -- Subtract the greatest square `u ^ 2` below `X`, then the greatest square `v ^ 2`
  -- below `X - u ^ 2`.
  refine ⟨4, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
  set m := ⌊X⌋₊ with hmdef
  have hm : (m : ℝ) ≤ X := Nat.floor_le (by linarith)
  have hm' : X < m + 1 := Nat.lt_floor_add_one X
  set u := Nat.sqrt m with hudef
  have hu1 : u * u ≤ m := Nat.sqrt_le m
  have hu2 : m < (u + 1) * (u + 1) := Nat.lt_succ_sqrt m
  set r := m - u * u with hrdef
  set v := Nat.sqrt r with hvdef
  have hv1 : v * v ≤ r := Nat.sqrt_le r
  have hv2 : r < (v + 1) * (v + 1) := Nat.lt_succ_sqrt r
  have hr : r ≤ 2 * u := by
    have : (u + 1) * (u + 1) = u * u + 2 * u + 1 := by ring
    omega
  have hn : u ^ 2 + v ^ 2 ≤ m := by
    have := hv1; rw [sq, sq]; omega
  have hgap : m ≤ u ^ 2 + v ^ 2 + 2 * v := by
    have : (v + 1) * (v + 1) = v * v + 2 * v + 1 := by ring
    rw [sq, sq]; omega
  have hv4 : v ^ 4 ≤ 4 * m := by
    have h1 : v ^ 4 = (v * v) * (v * v) := by ring
    have h2 : v * v ≤ 2 * u := le_trans hv1 hr
    calc v ^ 4 = (v * v) * (v * v) := h1
      _ ≤ (2 * u) * (2 * u) := Nat.mul_le_mul h2 h2
      _ = 4 * (u * u) := by ring
      _ ≤ 4 * m := by omega
  set y := X ^ (1 / 4 : ℝ) with hydef
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have hy4 : y ^ 4 = X := by
    rw [hydef, ← Real.rpow_natCast, ← Real.rpow_mul hX0]; norm_num
  have hy1 : 1 ≤ y := Real.one_le_rpow hX (by norm_num)
  have hv4r : (v : ℝ) ^ 4 ≤ 4 * X := by
    have : ((v ^ 4 : ℕ) : ℝ) ≤ ((4 * m : ℕ) : ℝ) := by exact_mod_cast hv4
    push_cast at this; linarith
  have hvy : (v : ℝ) ≤ 3 / 2 * y := by
    by_contra h
    push Not at h
    have h0 : (0 : ℝ) ≤ 3 / 2 * y := by positivity
    have := pow_lt_pow_left₀ h h0 (by norm_num : (4 : ℕ) ≠ 0)
    have e : (3 / 2 * y) ^ 4 = 81 / 16 * y ^ 4 := by ring
    rw [e, hy4] at this
    linarith
  refine ⟨u ^ 2 + v ^ 2, ⟨u, v, rfl⟩, ?_, ?_⟩
  · have hg : (m : ℝ) ≤ ((u ^ 2 + v ^ 2 : ℕ) : ℝ) + 2 * v := by exact_mod_cast hgap
    nlinarith
  · have : ((u ^ 2 + v ^ 2 : ℕ) : ℝ) ≤ m := by exact_mod_cast hn
    linarith

end Green66
