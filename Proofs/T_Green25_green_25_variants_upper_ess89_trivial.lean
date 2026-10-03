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
# Green's Open Problem 25

References:
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.25)
- [ESS89] Erdős, Pál, András Sárközy, and V. T. Sós. "On a conjecture of Roth and some related
  problems I." Irregularities of partitions. Berlin, Heidelberg: Springer Berlin Heidelberg, 1989.
  47-59.
- [Ru04] Ruzsa, Imre Z. "A problem on restricted sumsets." CONTEMPORARY MATHEMATICS 342 (2004):
  245-248.
-/

@[expose] public section

open Asymptotics Filter Finset

namespace Green25

/--
For which values of $k$ is the following true: whenever we partition $[N] = A_1 \cup \dots \cup A_k$,
$\left|\bigcup^k_{i=1} (A_i \hat{+} A_i)\right| \geq \frac{1}{10} N$?
-/
def Property25 (k N : ℕ) : Prop :=
  1 ≤ k ∧ k ≤ N ∧
  ∀ P : Finpartition (Icc 1 N), #P.parts = k →
  10 * #(P.parts.biUnion Finset.restrictedSumset) ≥ N

/-- The best-known lower bound [ESS89]. -/
noncomputable def bestLower (N : ℕ) : ℝ := Real.log (Real.log N)

/-- The best-known upper bound [ESS89]. -/
noncomputable def bestUpper (N : ℕ) : ℝ := (N : ℝ) / Real.log N

/--
For which values of $k$ is the following true: whenever we partition $[N] = A_1 \cup \dots \cup A_k$,
$\left|\bigcup^k_{i=1} (A_i \hat{+} A_i)\right| \geq \frac{1}{10} N$?
-/
@[category research open, AMS 5 11]
theorem green_25 : {k : ℕ → ℕ | ∀ᶠ N in atTop, Property25 (k N) N} = answer(sorry) := by
  sorry

/-- We conjecture that the best-known upper bound can be lowered. -/
@[category research open, AMS 5 11]
theorem green_25.upper :
    let ans := (answer(sorry) : ℕ → ℕ)
    (∀ᶠ N in atTop, 1 ≤ ans N ∧ ans N ≤ N) ∧ -- Ensure k is a valid partition size
    (fun N => (ans N : ℝ)) =o[atTop] bestUpper ∧
    ¬ ∀ᶠ N in atTop, Property25 (ans N) N := by
  sorry

/-- We conjecture that the best-known lower bound can be raised. -/
@[category research open, AMS 5 11]
theorem green_25.lower :
    let ans := (answer(sorry) : ℕ → ℝ)
    (bestLower =o[atTop] ans) ∧
    (∀ᶠ N in atTop, 1 ≤ ans N ∧ ans N ≤ N) ∧
    ∀ k : ℕ → ℕ,
      (∀ᶠ N in atTop, 1 ≤ k N ∧ k N ≤ N) ∧
      ((fun N => (k N : ℝ)) ≪ ans) →
      ∀ᶠ N in atTop, Property25 (k N) N := by
  sorry

/--
For $k \ll \log \log N$, this is true [Gr24].

NOTE: [ESS89] derive a precise constant for which this is true, but $\ll$ would imply that it works
for any constant. We thus prefer a little-o statement.
 -/
@[category research solved, AMS 5 11]
theorem green_25.variants.lower_ess89 :
  ∀ k : ℕ → ℕ,
    (∀ᶠ N in atTop, 1 ≤ k N ∧ k N ≤ N) ∧ -- Ensure Property25 is not False due to non-existent partitions
    (fun N => (k N : ℝ)) =o[atTop] bestLower →
    ∀ᶠ N in atTop, Property25 (k N) N := by
  sorry

/--
For $k \gg N / \log N$, it need not be true [Gr24].

We formalize by enforcing a $N / \log N$ growth rate on $k(N)$. This avoids cases like $k(N) = N$
or $N-1$, which produce trivial counter examples with singletons and thus empty restricted sumsets.
-/
@[category research solved, AMS 5 11]
theorem green_25.variants.upper_ess89 :
  ∃ k : ℕ → ℕ,
    (∀ᶠ N in atTop, 1 ≤ k N ∧ k N ≤ N) ∧
    (fun N => (k N : ℝ)) =Θ[atTop] bestUpper ∧
    ¬ ∀ᶠ N in atTop, Property25 (k N) N := by
  sorry

lemma g25_not (N : ℕ) (hN : 1 ≤ N) : ¬ Property25 N N := by
  rintro ⟨-, -, h⟩
  have hd := h (⊥ : Finpartition (Icc 1 N)) (by
    rw [Finpartition.card_bot]; simp)
  have hempty : (⊥ : Finpartition (Icc 1 N)).parts.biUnion Finset.restrictedSumset = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_biUnion.mp hx
    rw [Finpartition.parts_bot, Finset.mem_map] at hs
    obtain ⟨a, -, rfl⟩ := hs
    simp [Finset.restrictedSumset] at hxs
  rw [hempty, card_empty] at hd
  omega

theorem g25_main : ∃ k : ℕ → ℕ,
    (∀ᶠ N in atTop, 1 ≤ k N ∧ k N ≤ N) ∧
    ((fun N => (k N : ℝ)) ≫ bestUpper) ∧
    ¬ ∀ᶠ N in atTop, Property25 (k N) N := by
  refine ⟨fun N => N, ?_, ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop 1] with N hN; exact ⟨hN, le_rfl⟩
  · refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 3] with N hN
    have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
    have hlog : 1 ≤ Real.log N := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have := Real.exp_one_lt_d9; linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs, bestUpper, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity), one_mul, div_le_iff₀ (by linarith)]
    nlinarith
  · intro h
    obtain ⟨N, hN⟩ := (h.and (eventually_ge_atTop 1)).exists
    exact g25_not N hN.2 hN.1

/--
For $k \gg N / \log N$, it need not be true [Gr24].

In this version, cases like $k(N) = N$ or $N-1$ can produce trivial counter examples.
-/
@[category research solved, AMS 5 11]
theorem green_25.variants.upper_ess89_trivial :
  ∃ k : ℕ → ℕ,
    (∀ᶠ N in atTop, 1 ≤ k N ∧ k N ≤ N) ∧
    ((fun N => (k N : ℝ)) ≫ bestUpper) ∧
    ¬ ∀ᶠ N in atTop, Property25 (k N) N := by
  exact g25_main

/--
For $k(N) = \lceil N^{23/40} \rceil$, it need not be true: for all sufficiently large $N$
there is a partition of $[N]$ into $\lceil N^{23/40} \rceil$ parts with
$\left|\bigcup^k_{i=1} (A_i \hat{+} A_i)\right| < \frac{1}{10} N$.
In particular, the best-known upper bound $N / \log N$ can be lowered.
-/
@[category research solved, AMS 5 11,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/green-25-upper-bound/blob/3a54a688dfc4d7b9c8990bbaeb1a124c075454e4/lean/Green25UpperFC.lean#L3043-L3051"]
theorem green_25.variants.upper_pow_23_40 :
    let k : ℕ → ℕ := fun N => Nat.ceil ((N : ℝ) ^ (23 / 40 : ℝ))
    (∀ᶠ N in atTop, 1 ≤ k N ∧ k N ≤ N) ∧
    (fun N => (k N : ℝ)) =o[atTop] bestUpper ∧
    ∀ᶠ N in atTop, ¬ Property25 (k N) N := by
  sorry

end Green25
