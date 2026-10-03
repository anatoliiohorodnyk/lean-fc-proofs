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
# Erdős Problem 261

*References:*
 - [erdosproblems.com/261](https://www.erdosproblems.com/261)
 - [BoLo90] Borwein, Peter and Loring, Terry A., Some questions of Erdős and Graham on numbers
    of the form $\sum g_n/2^{g_n}$. Math. Comp. (1990), 377--394.
 - [Er88c] Erdős, P., On the irrationality of certain series: problems and results. New advances
    in transcendence theory (Durham, 1986) (1988), 102--109.
 - [TUZ20] Tengely, Szabolcs and Ulas, Maciej and Zygadlo, Jakub, On a Diophantine equation of
    Erdős and Graham. J. Number Theory (2020), 445--459.
-/

@[expose] public section

open scoped Cardinal

namespace Erdos261

/-- A natural number $n$ is said to have property `Erdos261Prop` if there exist $t \ge 2$
pairwise distinct positive integers $a_1, \ldots, a_t$ such that
$n / 2^n = \sum_{1 \le k \le t} a_k / 2^{a_k}$. -/
def Erdos261Prop (n : ℕ) : Prop := ∃ᵉ (t ≥ 2) (a : Fin t → ℕ), a.Injective ∧
  (1 ≤ a) ∧ n / (2 ^ n : ℚ) = ∑ k, (a k) / (2 ^ (a k) : ℚ)

/-- A canonical infinite representation of a rational number $x$ by positive integers. The
denominators are strictly increasing so that reorderings are not counted as different
representations. -/
def Erdos261InfiniteRepresentation (x : ℚ) (a : ℕ → ℕ) : Prop :=
  StrictMono a ∧ (1 ≤ a) ∧ Summable (fun k => (a k) / (2 ^ (a k) : ℚ)) ∧
    x = ∑' k, (a k) / (2 ^ (a k) : ℚ)

/-- For every positive integer $m$, if $n = 2^{m+1} - m - 2$, then
$$\frac{n}{2^n} = \sum_{n < k \le n + m} \frac{k}{2^k}.$$

This construction is due to Borwein and Loring [BoLo90]. -/
@[category textbook, AMS 11]
theorem erdos_261.variants.borwein_loring (m : ℕ) (hm : 0 < m) :
    let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ) := by
  sorry

/-- The Borwein--Loring construction gives the required property when $m \ge 2$. This lower
bound ensures that the representation contains at least two terms. -/
@[category textbook, AMS 11]
theorem erdos_261.variants.borwein_loring_property (m : ℕ) (hm : 2 ≤ m) :
    Erdos261Prop (2 ^ (m + 1) - m - 2) := by
  sorry

lemma e261_geo (n m : ℕ) : ∑ k ∈ Finset.range m, ((n + 1 + k : ℕ) : ℚ) / 2 ^ (n + 1 + k) =
    (n + 2) / 2 ^ n - (n + m + 2) / 2 ^ (n + m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    rw [show n + 1 + m = n + m + 1 by ring, pow_succ]
    field_simp
    ring

lemma e261_pow (m : ℕ) : m + 2 ≤ 2 ^ (m + 1) := by
  induction m with
  | zero => norm_num
  | succ m ih => rw [pow_succ]; omega

lemma e261_prop (m : ℕ) (hm : 2 ≤ m) : Erdos261Prop (2 ^ (m + 1) - m - 2) := by
  set n := 2 ^ (m + 1) - m - 2 with hn
  have hn' : n + m + 2 = 2 ^ (m + 1) := by have := e261_pow m; omega
  refine ⟨m, hm, fun i => n + 1 + i, fun i j h => Fin.ext (by simpa using h),
    fun i => by show 1 ≤ n + 1 + (i : ℕ); omega, ?_⟩
  rw [Fin.sum_univ_eq_sum_range (fun i => ((n + 1 + i : ℕ) : ℚ) / 2 ^ (n + 1 + i)) m, e261_geo]
  have hq : ((n : ℚ) + m + 2) = 2 ^ (m + 1) := by exact_mod_cast hn'
  rw [hq, pow_add]
  field_simp
  ring

/-- Are there infinitely many positive integers $n$ such that there exist some $t \ge 2$ and
distinct integers $a_1, \ldots, a_t \ge 1$ satisfying
$$\frac{n}{2^n} = \sum_{1 \le k \le t} \frac{a_k}{2^{a_k}}?$$

In [Er88c], Erdős notes that Cusick had a simple proof that infinitely many such $n$ exist. -/
@[category research solved, AMS 11]
theorem erdos_261.parts.i : answer(True) ↔ {n : ℕ | 0 < n ∧ Erdos261Prop n}.Infinite := by
  simp only [true_iff]
  have hmono : StrictMono (fun m : ℕ => 2 ^ (m + 3) - (m + 2) - 2) := by
    apply strictMono_nat_of_lt_succ
    intro m
    have h1 := e261_pow (m + 2)
    rw [show m + 2 + 1 = m + 3 by ring] at h1
    have h2 : 2 ^ (m + 1 + 3) = 2 * 2 ^ (m + 3) := by ring
    show 2 ^ (m + 3) - (m + 2) - 2 < 2 ^ (m + 1 + 3) - (m + 1 + 2) - 2
    omega
  refine Set.infinite_of_injective_forall_mem hmono.injective (fun m => ⟨?_, ?_⟩)
  · have h1 := e261_pow (m + 2)
    rw [show m + 2 + 1 = m + 3 by ring] at h1
    have h2 : 2 ^ (m + 3) = 2 * 2 ^ (m + 2) := by ring
    have h3 := e261_pow (m + 1)
    rw [show m + 1 + 1 = m + 2 by ring] at h3
    show 0 < 2 ^ (m + 3) - (m + 2) - 2
    omega
  · have := e261_prop (m + 2) (by omega)
    simpa [show m + 2 + 1 = m + 3 by ring] using this

/-- Tengely, Ulas, and Zygadlo [TUZ20] verified that every positive integer $n \le 10000$ has
the required property. -/
@[category research solved, AMS 11]
theorem erdos_261.variants.le_10000 {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000) :
    Erdos261Prop n := by
  sorry

/-- Do all positive integers $n$ have the required property? -/
@[category research open, AMS 11]
theorem erdos_261.parts.ii : answer(sorry) ↔ ∀ n > 0, Erdos261Prop n := by
  sorry

/-- Is there a rational number $x$ such that
$$x = \sum_{k=1}^{\infty} \frac{a_k}{2^{a_k}}$$
has at least $2^{\aleph_0}$ representations by pairwise distinct positive integers $a_k$? -/
@[category research open, AMS 11]
theorem erdos_261.parts.iii : answer(sorry) ↔ ∃ x : ℚ,
    𝔠 ≤ #{a : ℕ → ℕ | Erdos261InfiniteRepresentation x a} := by
  sorry

/-- In [Er88c], Erdős asks the weaker question of whether there exists a rational $x$ with at
least two representations
$$x = \sum_{k=1}^{\infty} \frac{a_k}{2^{a_k}}$$
by pairwise distinct positive integers $a_k$.

The answer is yes: Z. Rafik (erdosproblems.com forum, 27 Apr 2026) observed that
$4/2^4 = 5/2^5 + 6/2^6$ and $\sum_{m \ge 1} m/2^m = 2$, so $7/4$ is represented both by
$\mathbb{N}_{>0} \setminus \{4\}$ and by $\mathbb{N}_{>0} \setminus \{5, 6\}$. It is generally believed that
"two" here is a misprint for $2^{\aleph_0}$ (see `erdos_261.parts.iii`, which remains open). -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/g8r-b8/erdos261-lean/blob/976bddf21eafc93ea86a7a1bfd92b847070a6f31/Erdos261.lean#L87"]
theorem erdos_261.variants.two_representations : answer(True) ↔ ∃ x : ℚ,
    2 ≤ #{a : ℕ → ℕ | Erdos261InfiniteRepresentation x a} := by
  sorry

end Erdos261
