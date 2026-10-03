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
# Erdős Problem 292

*References:*
- [erdosproblems.com/292](https://www.erdosproblems.com/292)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [Ma00] Martin, Greg, *Denser Egyptian fractions*. Acta Arith. (2000), 231-260.
-/

@[expose] public section

open Filter Asymptotics

namespace Erdos292

/-- The set $A$ of $n\in \mathbb{N}$ such that there exist $1\leq m_1<\cdots <m_k=n$ with
$\sum\tfrac{1}{m_i}=1$. -/
def A : Set ℕ :=
  {n | ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 n ∧ n ∈ S ∧ ∑ m ∈ S, (1 : ℚ) / m = 1}

/--
Let $A$ be the set of $n\in \mathbb{N}$ such that there exist $1\leq m_1<\cdots <m_k=n$ with
$\sum\tfrac{1}{m_i}=1$. Explore $A$. In particular, does $A$ have density $1$?

Straus observed that $A$ is closed under multiplication. Furthermore, it is easy to see that $A$
does not contain any prime power.

The answer is yes, as proved by Martin [Ma00], who in fact proved that if
$B=\mathbb{N}\backslash A$ then, for all large $x$,
$$\frac{\lvert B\cap [1,x]\rvert}{x}\asymp \frac{\log\log x}{\log x},$$
and also gave an essentially complete description of $B$ as those integers which are small
multiples of prime powers.

van Doorn has observed that if $n\in A$ (with $n>1$) then $2n\in A$ also, since if
$\sum \frac{1}{m_i}=1$ then $\frac{1}{2}+\sum\frac{1}{2m_i}=1$ also.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos292.lean#L116"]
theorem erdos_292 : answer(True) ↔ A.HasDensity 1 := by
  sorry

/-- Martin [Ma00] proved that if $B=\mathbb{N}\backslash A$ then
$\frac{\lvert B\cap [1,x]\rvert}{x}\asymp \frac{\log\log x}{\log x}$. -/
@[category research solved, AMS 11]
theorem erdos_292.variants.martin :
    (fun x : ℕ ↦ ((Aᶜ ∩ Set.Icc 1 x).ncard : ℝ) / x) =Θ[atTop]
      fun x ↦ Real.log (Real.log x) / Real.log x := by
  sorry

lemma e292_pos {n : ℕ} (hn : n ∈ A) : 1 ≤ n := by
  obtain ⟨S, hS, hnS, -⟩ := hn
  exact (Finset.mem_Icc.mp (hS hnS)).1

/-- Straus observed that $A$ is closed under multiplication. -/
@[category research solved, AMS 11]
theorem erdos_292.variants.mul : ∀ m ∈ A, ∀ n ∈ A, m * n ∈ A := by
  classical
  intro m hm n hn
  have hm1 := e292_pos hm
  have hn1 := e292_pos hn
  obtain ⟨S, hS, hmS, hsum⟩ := hm
  obtain ⟨T, hT, hnT, htsum⟩ := hn
  set T' := T.image (fun t => m * t)
  have hdisj : Disjoint (S.erase m) T' := by
    rw [Finset.disjoint_left]
    intro x hx hxT
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hxT
    have h1 := Finset.mem_Icc.mp (hS (Finset.mem_of_mem_erase hx))
    have h2 := (Finset.mem_Icc.mp (hT ht)).1
    have h3 := Finset.ne_of_mem_erase hx
    have : m ≤ m * t := Nat.le_mul_of_pos_right m h2
    have : m * t ≤ m := h1.2
    apply h3; omega
  refine ⟨S.erase m ∪ T', ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · have := Finset.mem_Icc.mp (hS (Finset.mem_of_mem_erase h))
      rw [Finset.mem_Icc]; exact ⟨this.1, this.2.trans (Nat.le_mul_of_pos_right m hn1)⟩
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp h
      have := Finset.mem_Icc.mp (hT ht)
      rw [Finset.mem_Icc]
      exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)),
        Nat.mul_le_mul_left m this.2⟩
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨n, hnT, rfl⟩)
  · rw [Finset.sum_union hdisj, Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hm1 h)]
    have h1 : ∑ x ∈ S.erase m, (1 : ℚ) / x = 1 - 1 / m := by
      have := Finset.add_sum_erase S (fun x : ℕ => (1 : ℚ) / x) hmS
      rw [hsum] at this; linarith
    have h2 : ∑ x ∈ T, (1 : ℚ) / ((m * x : ℕ) : ℚ) = 1 / m := by
      have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
      calc ∑ x ∈ T, (1 : ℚ) / ((m * x : ℕ) : ℚ) = ∑ x ∈ T, (1 / m) * ((1 : ℚ) / x) := by
            refine Finset.sum_congr rfl (fun x _ => ?_); push_cast; field_simp
        _ = 1 / m := by rw [← Finset.mul_sum, htsum, mul_one]
    rw [h1, h2]; ring

/-- $A$ does not contain any prime power. -/
@[category research solved, AMS 11]
theorem erdos_292.variants.prime_pow : ∀ n ∈ A, ¬ IsPrimePow n := by
  sorry

/-- van Doorn observed that if $n\in A$ (with $n>1$) then $2n\in A$ also. -/
@[category research solved, AMS 11]
theorem erdos_292.variants.two_mul : ∀ n ∈ A, 1 < n → 2 * n ∈ A := by
  sorry

end Erdos292
