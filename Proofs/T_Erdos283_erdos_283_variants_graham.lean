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
# Erdős Problem 283

*References:*
- [erdosproblems.com/283](https://www.erdosproblems.com/283)
- [Al19] Alekseyev, Max A., On partitions into squares of distinct integers whose
reciprocals sum to 1. (2019), 213--221.
- [Ca60] Cassels, J. W. S., On the representation of integers as the sums of distinct summands taken from a fixed set. Acta Sci. Math. (Szeged) (1960), 111-124.
- [Gr63] Graham, R. L., A theorem on partitions. J. Austral. Math. Soc. (1963), 435-441.
- [vD25] W. van Doorn, Partitions with prescribed sum of rationals: asymptotic bounds. arXiv:2502.02200 (2025).
-/

@[expose] public section

open Filter Polynomial Finset

namespace Erdos283

/--
Given a polynomial `p` with rational coefficients, the predicate that if `p` takes integer values
at all integers, the leading coefficient is positive and there exists no $d≥2$ with $d ∣ p(n)$ for
all $n≥1$, then for all sufficiently large $m$, there exist integers $1≤n_1<\dots < n_k$ such that
$$1=\frac{1}{n_1}+\cdots+\frac{1}{n_k}$$ and $$m=p(n_1)+\cdots+p(n_k)$$?
-/
def Condition (p : ℚ[X]) : Prop :=
  (∀ n : ℤ, ∃ z : ℤ, p.eval (n : ℚ) = z) → p.leadingCoeff > 0 →
  ¬ (∃ d : ℤ, d ≥ 2 ∧ ∀ n : ℤ, n ≥ 1 → ∃ z : ℤ, p.eval (n : ℚ) = d * z) →
  ∀ᶠ (m : ℤ) in atTop, ∃ k ≥ 1, ∃ n : Fin (k + 1) → ℤ, 0 = n 0 ∧ StrictMono n ∧
  1 = ∑ i ∈ Finset.Icc 1 (Fin.last k), (1 : ℚ) / (n i) ∧
  (m : ℚ) = ∑ i ∈ Finset.Icc 1 (Fin.last k), p.eval (n i : ℚ)

/--
Let $p\colon \mathbb{Z} \rightarrow \mathbb{Z}$ be a polynomial (with rational coefficients,
taking integer values at all integers) whose leading coefficient is positive and such that there
exists no $d≥2$ with $d ∣ p(n)$ for all $n≥1$. Is it true that,
for all sufficiently large $m$, there exist integers $1≤n_1<\dots < n_k$ such that
$$1=\frac{1}{n_1}+\cdots+\frac{1}{n_k}$$
and
$$m=p(n_1)+\cdots+p(n_k)$$?

GPT 5.5 Pro (prompted by Price) has given a proof that the answer is yes, for the stronger version
with $1$ replaced by any rational $\alpha>0$.

This was formalized in Lean by Ammanamanchi using Opus 4.6 and GPT 5.5 Pro.
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at "https://github.com/Shashi456/erdos-formalizations/blob/286f856aa3fc08957b80950fd18a45aab8d045ea/Erdos/P283/Proof_flat.lean#L9738-L9746"]
theorem erdos_283 : answer(True) ↔ ∀ p : ℚ[X], Condition p := by
  sorry

def e283Good (l : List ℕ) : Prop :=
  l.Nodup ∧ 0 ∉ l ∧ 1 ∉ l ∧ 3 ∉ l ∧ (l.map (fun d : ℕ => (1 : ℚ) / d)).sum = 1

def e283Rep (m : ℕ) : Prop := ∃ l : List ℕ, e283Good l ∧ l.sum = m

def e283Data : List (List ℕ) :=
  [[2, 4, 8, 15, 30, 40],
  [2, 6, 7, 8, 21, 56],
  [2, 4, 5, 30, 60],
  [2, 4, 8, 16, 24, 48],
  [2, 7, 9, 10, 15, 18, 42],
  [2, 4, 7, 21, 28, 42],
  [2, 4, 7, 20, 30, 42],
  [2, 5, 6, 12, 36, 45],
  [2, 6, 7, 14, 20, 28, 30],
  [2, 5, 6, 15, 20, 60],
  [2, 6, 8, 9, 12, 72],
  [2, 4, 6, 14, 84],
  [2, 6, 9, 12, 16, 18, 48],
  [2, 4, 8, 14, 28, 56],
  [2, 4, 8, 15, 24, 60],
  [2, 4, 7, 21, 24, 56],
  [2, 5, 6, 12, 30, 60],
  [2, 5, 8, 9, 20, 72],
  [2, 6, 9, 10, 15, 30, 45],
  [2, 5, 9, 16, 18, 20, 48],
  [2, 7, 8, 10, 15, 21, 56],
  [2, 5, 8, 15, 20, 30, 40],
  [2, 7, 8, 9, 18, 21, 56],
  [2, 6, 9, 12, 15, 18, 60],
  [2, 4, 9, 12, 24, 72],
  [2, 4, 8, 12, 42, 56],
  [2, 6, 9, 10, 18, 20, 60],
  [2, 4, 8, 12, 40, 60],
  [2, 6, 8, 12, 15, 24, 60],
  [2, 8, 9, 10, 12, 15, 72],
  [2, 4, 10, 14, 15, 84],
  [2, 4, 9, 10, 45, 60],
  [2, 5, 6, 14, 20, 84],
  [2, 6, 7, 14, 15, 28, 60],
  [2, 5, 8, 14, 20, 28, 56],
  [2, 4, 8, 12, 36, 72],
  [2, 5, 7, 20, 21, 24, 56],
  [2, 5, 6, 15, 18, 90],
  [2, 4, 9, 10, 40, 72],
  [2, 6, 9, 10, 15, 24, 72],
  [4, 6, 7, 8, 10, 12, 15, 21, 56],
  [2, 7, 8, 9, 14, 28, 72],
  [2, 5, 8, 12, 24, 30, 60],
  [2, 4, 12, 15, 21, 28, 60],
  [2, 6, 10, 12, 14, 15, 84],
  [2, 4, 6, 24, 36, 72],
  [2, 6, 9, 12, 14, 18, 84],
  [2, 6, 8, 9, 21, 28, 72],
  [2, 4, 7, 15, 35, 84],
  [2, 5, 9, 12, 15, 45, 60],
  [2, 6, 8, 10, 15, 36, 72],
  [2, 5, 7, 10, 21, 105],
  [2, 4, 9, 10, 36, 90],
  [2, 5, 9, 14, 18, 20, 84],
  [2, 4, 7, 14, 42, 84],
  [4, 5, 6, 8, 12, 15, 20, 24, 60],
  [2, 5, 9, 12, 15, 40, 72],
  [2, 7, 8, 12, 20, 21, 30, 56],
  [2, 5, 10, 12, 18, 20, 90],
  [2, 6, 8, 10, 18, 24, 90],
  [2, 4, 7, 20, 21, 105],
  [4, 6, 7, 8, 9, 12, 14, 28, 72],
  [2, 6, 7, 12, 15, 35, 84],
  [2, 5, 8, 15, 18, 24, 90],
  [2, 5, 8, 10, 30, 36, 72],
  [2, 6, 7, 9, 14, 126],
  [2, 6, 9, 10, 12, 36, 90],
  [2, 4, 12, 14, 20, 30, 84],
  [2, 4, 6, 20, 45, 90],
  [2, 5, 7, 15, 20, 35, 84],
  [2, 4, 7, 16, 28, 112],
  [2, 5, 6, 10, 42, 105],
  [2, 4, 12, 15, 18, 30, 90],
  [2, 5, 9, 10, 20, 36, 90],
  [2, 6, 7, 12, 20, 21, 105],
  [2, 4, 9, 12, 21, 126],
  [2, 6, 7, 10, 18, 42, 90],
  [2, 5, 10, 12, 14, 28, 105],
  [2, 4, 6, 18, 63, 84],
  [2, 6, 7, 14, 16, 21, 112],
  [2, 4, 6, 20, 42, 105],
  [2, 4, 6, 18, 60, 90],
  [2, 6, 7, 10, 21, 30, 105],
  [4, 5, 6, 8, 12, 15, 18, 24, 90],
  [2, 7, 9, 10, 14, 15, 126],
  [2, 5, 8, 10, 24, 45, 90],
  [2, 4, 12, 14, 20, 28, 105],
  [2, 4, 9, 15, 30, 36, 90],
  [4, 5, 6, 7, 14, 15, 18, 28, 90],
  [2, 4, 10, 16, 18, 48, 90],
  [2, 4, 7, 14, 36, 126],
  [2, 7, 8, 9, 14, 24, 126],
  [4, 5, 6, 7, 9, 14, 20, 126],
  [2, 4, 8, 16, 18, 144],
  [2, 4, 10, 14, 28, 30, 105],
  [2, 5, 7, 12, 28, 35, 105],
  [2, 4, 6, 21, 36, 126],
  [2, 6, 8, 9, 21, 24, 126],
  [2, 7, 10, 14, 15, 16, 21, 112],
  [2, 4, 10, 15, 20, 42, 105],
  [2, 7, 9, 14, 16, 18, 21, 112],
  [2, 4, 7, 12, 70, 105],
  [2, 5, 6, 18, 20, 60, 90],
  [2, 4, 12, 14, 16, 42, 112],
  [2, 6, 7, 12, 14, 36, 126],
  [2, 7, 8, 14, 16, 21, 24, 112],
  [4, 5, 6, 7, 14, 16, 20, 21, 112],
  [2, 6, 8, 12, 16, 18, 144],
  [2, 4, 9, 14, 28, 45, 105],
  [4, 5, 6, 7, 10, 20, 21, 30, 105],
  [2, 7, 8, 12, 16, 24, 28, 112],
  [2, 5, 7, 14, 20, 36, 126],
  [2, 6, 7, 8, 28, 48, 112],
  [2, 4, 9, 20, 21, 30, 126],
  [2, 5, 8, 16, 18, 20, 144],
  [2, 4, 7, 12, 63, 126],
  [2, 8, 9, 10, 15, 21, 24, 126],
  [2, 5, 6, 20, 21, 36, 126],
  [2, 4, 8, 14, 21, 168],
  [2, 5, 9, 10, 12, 180],
  [2, 7, 9, 12, 14, 21, 28, 126],
  [2, 4, 12, 16, 18, 24, 144],
  [2, 6, 8, 9, 16, 36, 144],
  [2, 4, 8, 12, 28, 168],
  [4, 5, 6, 9, 10, 12, 21, 30, 126],
  [2, 7, 9, 12, 14, 18, 36, 126],
  [2, 8, 10, 12, 15, 16, 18, 144],
  [2, 4, 9, 16, 21, 48, 126],
  [2, 4, 9, 12, 20, 180],
  [2, 6, 10, 12, 15, 21, 36, 126],
  [2, 6, 7, 10, 15, 63, 126],
  [4, 5, 6, 7, 12, 14, 20, 36, 126],
  [2, 6, 8, 12, 14, 21, 168],
  [2, 4, 6, 24, 28, 168],
  [4, 5, 6, 8, 12, 16, 18, 20, 144],
  [2, 4, 10, 16, 18, 40, 144],
  [2, 4, 9, 10, 30, 180],
  [2, 6, 7, 8, 24, 63, 126],
  [2, 6, 8, 10, 15, 28, 168],
  [2, 5, 8, 14, 20, 21, 168],
  [2, 5, 6, 10, 36, 180],
  [2, 8, 9, 10, 15, 16, 36, 144],
  [4, 5, 6, 8, 10, 16, 18, 30, 144],
  [2, 6, 9, 10, 15, 20, 180],
  [2, 5, 8, 12, 20, 28, 168],
  [2, 4, 6, 16, 72, 144],
  [2, 4, 12, 14, 21, 24, 168],
  [4, 5, 6, 8, 9, 10, 24, 180],
  [2, 5, 9, 16, 20, 21, 48, 126],
  [2, 4, 6, 20, 36, 180],
  [2, 6, 8, 9, 20, 24, 180],
  [2, 8, 10, 12, 14, 15, 21, 168],
  [2, 4, 10, 15, 24, 28, 168],
  [2, 8, 9, 12, 14, 18, 21, 168],
  [2, 5, 9, 12, 15, 30, 180],
  [2, 8, 10, 12, 15, 21, 24, 36, 126],
  [2, 4, 6, 18, 45, 180],
  [2, 5, 9, 10, 20, 30, 180],
  [2, 5, 9, 12, 14, 35, 180],
  [4, 5, 6, 8, 12, 14, 20, 21, 168],
  [2, 4, 10, 14, 21, 40, 168],
  [2, 5, 9, 10, 18, 36, 180],
  [2, 6, 7, 8, 28, 42, 168],
  [2, 5, 6, 9, 60, 180]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma e283_data_good : ∀ l ∈ e283Data, l.Nodup ∧ 0 ∉ l ∧ 1 ∉ l ∧ 3 ∉ l ∧
    (l.map (fun d : ℕ => (1 : ℚ) / d)).sum = 1 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma e283_data_cover : ∀ m : Fin 164, ∃ l ∈ e283Data, l.sum = m.val + 99 := by decide +kernel

lemma e283_base (m : ℕ) (h1 : 99 ≤ m) (h2 : m ≤ 262) : e283Rep m := by
  obtain ⟨l, hl, hs⟩ := e283_data_cover ⟨m - 99, by omega⟩
  exact ⟨l, e283_data_good l hl, by simp at hs; omega⟩

lemma e283_step (T : List ℕ) (hT : T.Nodup) (hT0 : 0 ∉ T) (hT1 : 1 ∉ T) (hT3 : 3 ∉ T)
    (hTrec : (T.map (fun d : ℕ => (1 : ℚ) / d)).sum = 1 / 2)
    (hTdisj : ∀ x ∈ T, ∀ a : ℕ, x = 2 * a → a = 0 ∨ a = 1 ∨ a = 3)
    (hTodd : ∀ x ∈ T, x = 1 ∨ x = 3 → False)
    (m : ℕ) (hm : e283Rep m) : e283Rep (T.sum + 2 * m) := by
  obtain ⟨l, ⟨hnd, h0, h1, h3, hrec⟩, hs⟩ := hm
  refine ⟨T ++ l.map (2 * ·), ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [List.nodup_append]
    refine ⟨hT, hnd.map (fun a b h => by simpa using h), ?_⟩
    intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
    rcases hTdisj x hx a hxy with rfl | rfl | rfl
    · exact h0 ha
    · exact h1 ha
    · exact h3 ha
  · intro h
    rcases List.mem_append.mp h with h | h
    · exact hT0 h
    · obtain ⟨a, ha, hz⟩ := List.mem_map.mp h
      have : a = 0 := by omega
      exact h0 (this ▸ ha)
  · intro h
    rcases List.mem_append.mp h with h | h
    · exact hT1 h
    · obtain ⟨a, ha, hz⟩ := List.mem_map.mp h; omega
  · intro h
    rcases List.mem_append.mp h with h | h
    · exact hT3 h
    · obtain ⟨a, ha, hz⟩ := List.mem_map.mp h; omega
  · rw [List.map_append, List.sum_append, hTrec, List.map_map]
    have : (l.map ((fun d : ℕ => (1 : ℚ) / d) ∘ (2 * ·))) =
        (l.map (fun d : ℕ => (1 : ℚ) / d)).map (fun q => q * (1 / 2)) := by
      rw [List.map_map]; apply List.map_congr_left; intro a _
      simp only [Function.comp]; push_cast; field_simp
    rw [this, List.sum_map_mul_right, List.map_id', hrec]
    norm_num
  · rw [List.sum_append, List.sum_map_mul_left, List.map_id', hs]

lemma e283_stepE (m : ℕ) (hm : e283Rep m) : e283Rep (2 * m + 2) := by
  have := e283_step [2] (by decide) (by decide) (by decide) (by decide) (by norm_num)
    (by intro x hx a hxa; simp at hx; omega) (by intro x hx; simp at hx; omega) m hm
  simpa [add_comm] using this

lemma e283_stepO (m : ℕ) (hm : e283Rep m) : e283Rep (2 * m + 65) := by
  have := e283_step [5, 6, 9, 45] (by decide) (by decide) (by decide) (by decide) (by norm_num)
    (by intro x hx a hxa; simp at hx; omega) (by intro x hx; simp at hx; omega) m hm
  simpa [add_comm] using this

lemma e283_all : ∀ m, 99 ≤ m → e283Rep m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    by_cases h : m ≤ 262
    · exact e283_base m hm h
    · rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
      · have := e283_stepE (k - 1) (ih (k - 1) (by omega) (by omega))
        rwa [show 2 * (k - 1) + 2 = m by omega] at this
      · have := e283_stepO (k - 32) (ih (k - 32) (by omega) (by omega))
        rwa [show 2 * (k - 32) + 65 = m by omega] at this

/-- Summing a function vanishing at `0` over `Icc 1 (last k)` = over the shifted embedding. -/
lemma e283_sum_bridge (k : ℕ) (e : Fin k → ℕ) (g : ℤ → ℚ) (hg : g 0 = 0) :
    ∑ i ∈ Finset.Icc 1 (Fin.last k), g ((Fin.cons (0 : ℤ) (fun i => (e i : ℤ)) : Fin (k + 1) → ℤ) i)
      = ∑ i : Fin k, g (e i) := by
  set G : Fin (k + 1) → ℚ := fun i => g ((Fin.cons (0 : ℤ) (fun i => (e i : ℤ)) : Fin (k + 1) → ℤ) i)
  have h1 : ∑ i ∈ Finset.Icc 1 (Fin.last k), G i = ∑ i : Fin (k + 1), G i := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    have : i = 0 := by
      by_contra h
      apply hi
      rw [Finset.mem_Icc]
      exact ⟨Fin.one_le_of_ne_zero h, Fin.le_last _⟩
    subst this; simp [G, hg]
  show ∑ i ∈ Finset.Icc 1 (Fin.last k), G i = _
  rw [h1, Fin.sum_univ_succ]
  simp [G, hg]

lemma e283_bridge (m : ℕ) (hm : e283Rep m) (hm1 : 1 ≤ m) :
    ∃ k ≥ 1, ∃ n : Fin (k + 1) → ℤ, 0 = n 0 ∧ StrictMono n ∧
      1 = ∑ i ∈ Finset.Icc 1 (Fin.last k), (1 : ℚ) / (n i) ∧
      ((m : ℤ) : ℚ) = ∑ i ∈ Finset.Icc 1 (Fin.last k), (X : ℚ[X]).eval (n i : ℚ) := by
  obtain ⟨l, ⟨hnd, h0, -, -, hrec⟩, hs⟩ := hm
  set S := l.toFinset with hS
  set k := S.card with hk
  let e := S.orderEmbOfFin rfl
  have he : ∀ i, e i ∈ S := fun i => S.orderEmbOfFin_mem rfl i
  have hepos : ∀ i, 0 < e i := fun i => by
    have := List.mem_toFinset.mp (he i)
    rcases Nat.eq_zero_or_pos (e i) with h | h
    · rw [h] at this; exact absurd this h0
    · exact h
  have hsumS : ∀ f : ℕ → ℚ, ∑ i : Fin k, f (e i) = ∑ s ∈ S, f s := by
    intro f
    conv_rhs => rw [← S.map_orderEmbOfFin_univ rfl]
    rw [Finset.sum_map]; rfl
  have hk1 : 1 ≤ k := by
    rw [hk, hS, List.card_toFinset, List.dedup_eq_self.mpr hnd]
    rcases l with _ | ⟨a, t⟩
    · simp at hs; omega
    · simp
  refine ⟨k, hk1, Fin.cons (0 : ℤ) (fun i => (e i : ℤ)), rfl, ?_, ?_, ?_⟩
  · intro i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact absurd hij (lt_irrefl _)
      | succ j => simp only [Fin.cons_zero, Fin.cons_succ]; exact_mod_cast hepos j
    | succ i =>
      induction j using Fin.cases with
      | zero => exact absurd hij (by simp [Fin.lt_def])
      | succ j =>
        simp only [Fin.cons_succ]
        exact_mod_cast e.strictMono (Fin.succ_lt_succ_iff.mp hij)
  · rw [e283_sum_bridge k e (fun z : ℤ => (1 : ℚ) / (z : ℚ)) (by simp)]
    have := hsumS (fun s : ℕ => (1 : ℚ) / (s : ℚ))
    simp only [Int.cast_natCast] at this ⊢
    rw [this, hS, List.sum_toFinset _ hnd, hrec]
  · rw [e283_sum_bridge k e (fun z : ℤ => (X : ℚ[X]).eval (z : ℚ)) (by simp)]
    have := hsumS (fun s : ℕ => (s : ℚ))
    simp only [eval_X, Int.cast_natCast] at this ⊢
    rw [this, hS, List.sum_toFinset _ hnd, ← hs]
    push_cast
    rfl

/--
Graham [Gr63] has proved this when $p(x)=x$.
-/
@[category research solved, AMS 11]
theorem erdos_283.variants.graham : Condition X := by
  intro _ _ _
  filter_upwards [eventually_ge_atTop (99 : ℤ)] with m hm
  have hm' : m = ((m.toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg (by omega)).symm
  rw [hm']
  exact e283_bridge m.toNat (e283_all _ (by omega)) (by omega)

/--
Graham also conjectures that this remains true with $1$ replaced by an arbitrary rational $\alpha>0$
(provided $m$ is taken sufficiently large depending on $\alpha$).
-/
@[category research solved, AMS 11]
theorem erdos_283.variants.graham_alpha :
  ∀ (p : ℚ[X]) (α : ℚ),
    (∀ n : ℤ, ∃ z : ℤ, p.eval (n : ℚ) = z) →
    0 < p.leadingCoeff →
    (¬ ∃ (d : ℤ), d ≥ 2 ∧ ∀ (n : ℤ), n ≥ 1 → ∃ z : ℤ, p.eval (n : ℚ) = d * z) →
    α > 0 →
    ∀ᶠ (m : ℕ) in atTop,
      ∃ S : Finset ℕ, (∀ n ∈ S, 1 ≤ n) ∧
        (∑ n ∈ S, (1 / (n : ℚ))) = α ∧
        (∑ n ∈ S, p.eval (n : ℚ)) = (m : ℚ) := by
  sorry

/--
Cassels [Ca60] has proved that these conditions on the polynomial imply every sufficiently large
integer is the sum of $p(n_i)$ with distinct $n_i$.
-/
@[category research solved, AMS 11]
theorem erdos_283.variants.cassels :
  ∀ (p : ℚ[X]),
    (∀ n : ℤ, ∃ z : ℤ, p.eval (n : ℚ) = z) →
    0 < p.leadingCoeff →
    (¬ ∃ (d : ℤ), d ≥ 2 ∧ ∀ (n : ℤ), n ≥ 1 → ∃ z : ℤ, p.eval (n : ℚ) = d * z) →
    ∀ᶠ (m : ℕ) in atTop,
      ∃ S : Finset ℕ, (∀ n ∈ S, 1 ≤ n) ∧
        (∑ n ∈ S, p.eval (n : ℚ)) = (m : ℚ) := by
  sorry

/--
Burr has proved this if $p(x)=x^k$ with $k\geq 1$ and if we allow $n_i=n_j$.
-/
@[category research solved, AMS 11]
theorem erdos_283.variants.burr :
  ∀ (k : ℕ), k ≥ 1 →
    ∀ᶠ (m : ℕ) in atTop,
      ∃ M : Multiset ℕ, (∀ n ∈ M, 1 ≤ n) ∧
        (M.map (fun n ↦ 1 / (n : ℚ))).sum = 1 ∧
        (M.map (fun n ↦ (n : ℤ)^k)).sum = (m : ℤ) := by
  sorry

/--
Alekseyev [Al19] has proved this when $p(x)=x^2$, for all $m>8542$.
-/
@[category research solved, AMS 11]
theorem erdos_283.variants.alekseyev :
  ∀ (m : ℕ), m > 8542 →
    ∃ S : Finset ℕ, (∀ n ∈ S, 1 ≤ n) ∧
      (∑ n ∈ S, (1 / (n : ℚ))) = 1 ∧
      (∑ n ∈ S, (n : ℤ)^2) = (m : ℤ) := by
  sorry

/--
van Doorn [vD25] has investigated the question of what 'sufficiently large' means for $p(x)=x$.
van Doorn has also proved the original conjecture for many linear and quadratic polynomials.
For example, if $p(x) = x + b$ with $1 \leq b \leq 5000$, then the conjecture is true.
-/
@[category research solved, AMS 11]
theorem erdos_283.variants.van_doorn_linear :
  ∀ b : ℤ, 1 ≤ b → b ≤ 5000 → Condition (X + C (b : ℚ)) := by
  sorry

/--
van Doorn [vD25] has proved the original conjecture for many linear and quadratic polynomials.
For example, if $p(x) = x^2 + b$ with $1 \leq b \leq 800$, then the conjecture is true.
-/
@[category research solved, AMS 11]
theorem erdos_283.variants.van_doorn_quadratic :
  ∀ b : ℤ, 1 ≤ b → b ≤ 800 → Condition (X^2 + C (b : ℚ)) := by
  sorry

end Erdos283
