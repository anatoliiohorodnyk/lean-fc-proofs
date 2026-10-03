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
# Erdős Problem 285

*Reference:* [erdosproblems.com/285](https://www.erdosproblems.com/285)
-/

@[expose] public section

open Filter

open scoped Topology Real

namespace Erdos285

/--
Let $f(k)$ be the minimal value of $n_k$ such that there exist $n_1 < n_2 < \dots < n_k$ with
$$
  1 = \frac{1}{n_1} + \cdots + \frac{1}{n_k}.
$$
Is it true that
$$
  f(k) = (1 + o(1)) \frac{e}{e - 1} k ?
$$

Proved by Martin [Ma00].

[Ma00] Martin, Greg, _Denser Egyptian fractions_. Acta Arith. (2000), 231-260.
-/
@[category research solved, AMS 5 11]
theorem erdos_285 :
    answer(True) ↔ ∀ᵉ (f : ℕ → ℕ)
    (S : Set ℕ)
    (hS : S = {k | ∃ (n : Fin k.succ → ℕ), StrictMono n ∧ 0 ∉ Set.range n ∧
      1 = ∑ i, (1 : ℝ) / n i })
    (h : ∀ k ∈ S,
      IsLeast
        { n (Fin.last k) | (n : Fin k.succ → ℕ) (_ : StrictMono n) (_ : 0 ∉ Set.range n)
          (_ : 1 = ∑ i, (1 : ℝ) / n i) }
        (f k)),
    ∃ (o : ℕ → ℝ) (_ : o =o[atTop] (1 : ℕ → ℝ)),
      ∀ k ∈ S, f k = (1 + o k) * rexp 1 / (rexp 1 - 1) * (k + 1) := by
  sorry

open Filter Real in
/-- `∑_{i ≤ k} 1/(a+i) ≥ log((a+k+1)/a)`. -/
lemma e285_harm (a k : ℕ) (ha : 1 ≤ a) :
    Real.log ((a + k + 1 : ℝ) / a) ≤ ∑ i ∈ Finset.range (k + 1), (1 : ℝ) / (a + i) := by
  induction k with
  | zero =>
    simp only [Finset.sum_range_one, Nat.cast_zero, add_zero, CharP.cast_eq_zero]
    have ha' : (0 : ℝ) < a := by exact_mod_cast ha
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (a + 1) / a by positivity)
    rw [show ((a : ℝ) + 1) / a - 1 = 1 / a by field_simp; ring] at this
    simpa using this
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have ha' : (0 : ℝ) < a := by exact_mod_cast ha
    have hpos : (0 : ℝ) < a + (k + 1) := by positivity
    have hstep := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (a + (k + 1) + 1) / (a + (k + 1)) by positivity)
    rw [show ((a : ℝ) + (k + 1) + 1) / (a + (k + 1)) - 1 = 1 / (a + (k + 1)) by field_simp; ring] at hstep
    have hsplit : Real.log ((a + (k + 1 : ℕ) + 1 : ℝ) / a) =
        Real.log ((a + k + 1 : ℝ) / a) + Real.log ((a + (k + 1) + 1) / (a + (k + 1))) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      congr 1; push_cast; field_simp; ring
    rw [hsplit]
    push_cast at ih ⊢
    linarith

open Filter Real in
lemma e285_gap (k : ℕ) (n : Fin k.succ → ℕ) (hn : StrictMono n) :
    ∀ i : Fin k.succ, n i + (k - i) ≤ n (Fin.last k) := by
  have key : ∀ j : ℕ, ∀ i : ℕ, (hi : i + j ≤ k) →
      n ⟨i, by omega⟩ + j ≤ n ⟨i + j, by omega⟩ := by
    intro j
    induction j with
    | zero => intro i _; simp
    | succ j ih =>
      intro i hi
      have h1 := ih i (by omega)
      have h2 : n ⟨i + j, by omega⟩ < n ⟨i + (j + 1), by omega⟩ := hn (by simp [Fin.lt_def])
      omega
  intro i
  have := key (k - i) i (by omega)
  have heq : (⟨(i : ℕ) + (k - i), by omega⟩ : Fin k.succ) = Fin.last k := by
    ext; simp; omega
  rw [heq] at this
  exact this

open Filter Real in
lemma e285_lower (k : ℕ) (n : Fin k.succ → ℕ) (hn : StrictMono n) (h0 : 0 ∉ Set.range n)
    (hsum : 1 = ∑ i, (1 : ℝ) / n i) :
    (rexp 1 * k + 1) / (rexp 1 - 1) ≤ n (Fin.last k) := by
  set N := n (Fin.last k)
  have hgap := e285_gap k n hn
  have hn0 : 1 ≤ n 0 := Nat.one_le_iff_ne_zero.mpr fun h => h0 ⟨0, h⟩
  have hNk : k + 1 ≤ N := by have := hgap 0; simp at this; omega
  set a := N - k
  have ha : 1 ≤ a := by omega
  have hle : ∀ i : Fin k.succ, (1 : ℝ) / (a + (i : ℕ)) ≤ 1 / n i := by
    intro i
    have hni : 1 ≤ n i := Nat.one_le_iff_ne_zero.mpr fun h => h0 ⟨i, h⟩
    have h1 : n i ≤ a + i := by have := hgap i; have := i.isLt; omega
    apply one_div_le_one_div_of_le (by exact_mod_cast hni)
    exact_mod_cast h1
  have hsum2 : ∑ i ∈ Finset.range (k + 1), (1 : ℝ) / (a + i) ≤ 1 := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => (1 : ℝ) / (a + i)) (k + 1)]
    calc ∑ i : Fin (k + 1), (1 : ℝ) / (a + (i : ℕ)) ≤ ∑ i, (1 : ℝ) / n i :=
          Finset.sum_le_sum fun i _ => hle i
      _ = 1 := hsum.symm
  have hlog := (e285_harm a k ha).trans hsum2
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  rw [Real.log_le_iff_le_exp (by positivity)] at hlog
  rw [div_le_iff₀ ha'] at hlog
  have haN : (a : ℝ) + k = N := by
    have : a + k = N := by omega
    exact_mod_cast this
  have he : 1 < rexp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  rw [div_le_iff₀ (by linarith)]
  nlinarith

open Filter Real in
theorem e285_main (f : ℕ → ℕ) (S : Set ℕ)
    (hS : S = {k | ∃ (n : Fin k.succ → ℕ), StrictMono n ∧ 0 ∉ Set.range n ∧
      1 = ∑ i, (1 : ℝ) / n i })
    (h : ∀ k ∈ S,
      IsLeast
        { n (Fin.last k) | (n : Fin k.succ → ℕ) (_ : StrictMono n) (_ : 0 ∉ Set.range n)
          (_ : 1 = ∑ i, (1 : ℝ) / n i) }
        (f k)) :
    ∃ (o : ℕ → ℝ) (_ : o =o[atTop] (1 : ℕ → ℝ)),
      ∀ k ∈ S, (1 + o k) * rexp 1 / (rexp 1 - 1) * (k + 1) ≤ f k := by
  have he : 1 < rexp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have he0 : 0 < rexp 1 := Real.exp_pos 1
  refine ⟨fun k => (1 - rexp 1) / rexp 1 * (1 / ((k : ℝ) + 1)), ?_, ?_⟩
  · show (fun k : ℕ => (1 - rexp 1) / rexp 1 * (1 / ((k : ℝ) + 1))) =o[atTop] (fun _ => (1 : ℝ))
    rw [Asymptotics.isLittleO_one_iff]
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul ((1 - rexp 1) / rexp 1)
    simpa using this
  · intro k hk
    obtain ⟨n, hn, h0, hsum, hfk⟩ := (h k hk).1
    rw [← hfk]
    have hl := e285_lower k n hn h0 hsum
    have hk1 : (0 : ℝ) < k + 1 := by positivity
    calc (1 + (1 - rexp 1) / rexp 1 * (1 / ((k : ℝ) + 1))) * rexp 1 / (rexp 1 - 1) * (k + 1)
        = (rexp 1 * k + 1) / (rexp 1 - 1) := by
          field_simp
          ring
      _ ≤ _ := hl

/--
It is trivial that $f(k)\geq (1 + o(1)) \frac{e}{e - 1}k$.
-/
@[category research solved, AMS 5 11]
theorem erdos_285.variants.lb (f : ℕ → ℕ)
    (S : Set ℕ)
    (hS : S = {k | ∃ (n : Fin k.succ → ℕ), StrictMono n ∧ 0 ∉ Set.range n ∧
      1 = ∑ i, (1 : ℝ) / n i })
    (h : ∀ k ∈ S,
      IsLeast
        { n (Fin.last k) | (n : Fin k.succ → ℕ) (_ : StrictMono n) (_ : 0 ∉ Set.range n)
          (_ : 1 = ∑ i, (1 : ℝ) / n i) }
        (f k)) :
    ∃ (o : ℕ → ℝ) (_ : o =o[atTop] (1 : ℕ → ℝ)),
      ∀ k ∈ S, (1 + o k) * rexp 1 / (rexp 1 - 1) * (k + 1) ≤ f k := by
  exact e285_main f S hS h

end Erdos285
