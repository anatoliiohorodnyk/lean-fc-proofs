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

/-- Straus observed that $A$ is closed under multiplication. -/
@[category research solved, AMS 11]
theorem erdos_292.variants.mul : ∀ m ∈ A, ∀ n ∈ A, m * n ∈ A := by
  sorry

/-- $A$ does not contain any prime power. -/
@[category research solved, AMS 11]
theorem erdos_292.variants.prime_pow : ∀ n ∈ A, ¬ IsPrimePow n := by
  classical
  intro n hn hpp
  obtain ⟨S, hS, hnS, hsum⟩ := hn
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
  have : Fact p.Prime := ⟨hp⟩
  set F : ℕ → ℚ := fun i => 1 / (max i 1 : ℕ) with hF
  have hFpos : ∀ i, 0 < F i := fun i => by simp only [hF]; positivity
  have hFS : ∀ i ∈ S, F i = 1 / (i : ℚ) := by
    intro i hi
    have := (Finset.mem_Icc.mp (hS hi)).1
    simp only [hF]; rw [max_eq_left this]
  have hsumF : ∑ i ∈ S, F i = 1 := by rw [Finset.sum_congr rfl hFS, hsum]
  have hvn : padicValRat p (F (p ^ k)) = -(k : ℤ) := by
    rw [hFS _ hnS, one_div, padicValRat.inv, padicValRat.of_nat, padicValNat.prime_pow]
  have hsplit := Finset.add_sum_erase S F hnS
  rw [hsumF] at hsplit
  rcases (S.erase (p ^ k)).eq_empty_or_nonempty with hemp | hne
  · rw [hemp, Finset.sum_empty, add_zero, hFS _ hnS] at hsplit
    have : (p ^ k : ℕ) = 1 := by
      rw [one_div, inv_eq_one] at hsplit; exact_mod_cast hsplit
    have : 2 ≤ p ^ k := (Nat.one_lt_pow hk.ne' hp.one_lt)
    omega
  · have hlt : padicValRat p (F (p ^ k)) < padicValRat p (∑ i ∈ S.erase (p ^ k), F i) := by
      apply padicValRat.lt_sum_of_lt hne _ hFpos
      intro i hi
      have hiS := Finset.mem_of_mem_erase hi
      have hine := Finset.ne_of_mem_erase hi
      have hiI := Finset.mem_Icc.mp (hS hiS)
      rw [hvn, hFS _ hiS, one_div, padicValRat.inv, padicValRat.of_nat]
      have hv : padicValNat p i < k := by
        by_contra h
        push Not at h
        have h1 : p ^ k ∣ i := (pow_dvd_pow p h).trans pow_padicValNat_dvd
        have := Nat.le_of_dvd (by omega) h1
        omega
      omega
    have hsum0 : F (p ^ k) + ∑ i ∈ S.erase (p ^ k), F i ≠ 0 := by rw [hsplit]; norm_num
    have hR : ∑ i ∈ S.erase (p ^ k), F i ≠ 0 :=
      (Finset.sum_pos (fun i _ => hFpos i) hne).ne'
    have := padicValRat.add_eq_of_lt hsum0 (hFpos _).ne' hR hlt
    rw [hsplit, hvn, padicValRat.one] at this
    omega

/-- van Doorn observed that if $n\in A$ (with $n>1$) then $2n\in A$ also. -/
@[category research solved, AMS 11]
theorem erdos_292.variants.two_mul : ∀ n ∈ A, 1 < n → 2 * n ∈ A := by
  sorry

end Erdos292
