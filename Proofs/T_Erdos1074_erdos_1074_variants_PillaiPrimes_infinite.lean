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
# Erdős Problem 1074

*Reference:* [erdosproblems.com/1074](https://www.erdosproblems.com/1074)
-/

@[expose] public section

namespace Erdos1074

open scoped Nat
open Nat

/-- The EHS numbers (after Erdős, Hardy, and Subbarao) are those $m\geq 1$ such that there
exists a prime $p\not\equiv 1\pmod{m}$ such that $m! + 1 \equiv 0\pmod{p}$. -/
abbrev EHSNumbers : Set ℕ := {m | 1 ≤ m ∧ ∃ p, p.Prime ∧ ¬p ≡ 1 [MOD m] ∧ p ∣ m ! + 1}

/-- The Pillai primes are those primes $p$ such that there exists an $m \ge 1$ with
$p\not\equiv 1\pmod{m}$ such that $m! + 1 \equiv 0\pmod{p}$-/
abbrev PillaiPrimes : Set ℕ := {p | p.Prime ∧ ∃ m ≥ 1, ¬p ≡ 1 [MOD m] ∧ p ∣ m ! + 1}

@[category test, AMS 11]
theorem two_not_mem_pillaiPrimes : ¬ 2 ∈ PillaiPrimes := by
  norm_num
  intro m hm h
  exact (Nat.dvd_factorial (by decide) (hm.lt_of_ne (by bound))).modEq_zero_nat.add_right 1

@[category test, AMS 11]
theorem twentyThree_mem_pillaiPrimes : 23 ∈ PillaiPrimes := by
  norm_num
  use 14
  decide

/-- Let $S$ be the set of all $m\geq 1$ such that there exists a prime $p\not\equiv 1\pmod{m}$ such
that $m! + 1 \equiv 0\pmod{p}$. Does
$$
  \lim\frac{|S\cap[1, x]|}{x}
$$
exist? -/
@[category research open, AMS 11]
theorem erdos_1074.parts.i : answer(sorry) ↔ ∃ c, EHSNumbers.HasDensity c := by
  sorry

/-- Let $S$ be the set of all $m\geq 1$ such that there exists a prime $p\not\equiv 1\pmod{m}$ such
that $m! + 1 \equiv 0\pmod{p}$. What is
$$
  \lim\frac{|S\cap[1, x]|}{x}?
$$ -/
@[category research open, AMS 11]
theorem erdos_1074.parts.ii : EHSNumbers.HasDensity answer(sorry) := by
  sorry

/-- Similarly, if $P$ is the set of all primes $p$ such that there exists an $m$ with
$p\not\equiv 1\pmod{m}$ such that $m! + 1 \equiv 0\pmod{p}$, then does
$$
  \lim\frac{|P\cap[1, x]|}{\pi(x)}
$$
exist? -/
@[category research open, AMS 11]
theorem erdos_1074.parts.iii : answer(sorry) ↔ ∃ c, PillaiPrimes.HasDensity c {p | p.Prime} := by
  sorry

/-- Similarly, if $P$ is the set of all primes $p$ such that there exists an $m$ with
$p\not\equiv 1\pmod{m}$ such that $m! + 1 \equiv 0\pmod{p}$, then what is
$$
  \lim\frac{|P\cap[1, x]|}{\pi(x)}?
$$ -/
@[category research open, AMS 11]
theorem erdos_1074.parts.iv :
    PillaiPrimes.HasDensity answer(sorry) {p | p.Prime} := by
  sorry

/-- Pillai [Pi30] raised the question of whether there exist any primes in $P$. This was answered
by Chowla, who noted that, for example, $14! + 1 \equiv 18! + 1 \equiv 0 \pmod{23}$. -/
@[category test, AMS 11]
theorem erdos_1074.variants.mem_pillaiPrimes : 23 ∈ PillaiPrimes := by
  norm_num
  exact ⟨14, by decide⟩

/--
Erdős, Hardy, and Subbarao proved that $S$ is infinite.

Formal proof linked here provided by AlphaProof.
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mzhorvath1/formal-conjectures/blob/3dec597bd1a73778760b761712a1fc5fb24bc5d7/FormalConjectures/ErdosProblems/1074.lean#L99"]
theorem erdos_1074.variants.EHSNumbers_infinite : EHSNumbers.Infinite := by
  sorry

lemma e1074_desc (q k : ℕ) (hq : 1 ≤ q) (hk : k ≤ q - 1) :
    (((q - 1).descFactorial k : ℕ) : ZMod q) = (-1) ^ k * (k ! : ℕ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.descFactorial_succ, Nat.factorial_succ]
    push_cast
    rw [ih (by omega)]
    have : ((q - 1 - k : ℕ) : ZMod q) = -(k + 1) := by
      rw [show q - 1 - k = q - (k + 1) by omega, Nat.cast_sub (by omega)]
      simp [ZMod.natCast_self]
    rw [this]; ring

lemma e1074_big (a : ℕ) : ∃ q ∈ PillaiPrimes, a < q := by
  obtain ⟨P, ⟨hP, hP6⟩, haP⟩ :=
    (Nat.infinite_setOf_prime_modEq_one (by norm_num : (6 : ℕ) ≠ 0)).exists_gt (a + 5)
  have hP6' : P % 6 = 1 := hP6
  set q := (P ! + 1).minFac with hqdef
  have hq : q.Prime := Nat.minFac_prime (by have := Nat.factorial_pos P; omega)
  have hqd : q ∣ P ! + 1 := Nat.minFac_dvd _
  have hqP : P < q := by
    by_contra h
    have h1 : q ∣ P ! := hq.dvd_factorial.mpr (by omega)
    exact hq.not_dvd_one ((Nat.dvd_add_right h1).mp hqd)
  have hq2 : q ≠ 2 := by
    rintro h2
    rw [h2] at hqd
    have : 2 ∣ P ! := Nat.dvd_factorial (by norm_num) (by omega)
    exact absurd ((Nat.dvd_add_right this).mp hqd) (by norm_num)
  have hqodd : q % 2 = 1 := (hq.eq_two_or_odd).resolve_left hq2
  by_cases hmod : q ≡ 1 [MOD P]
  · have hPd : P ∣ q - 1 := (Nat.modEq_iff_dvd' (by omega)).mp hmod.symm
    set k := q - 1 - P with hk
    have hkodd : k % 2 = 1 := by omega
    -- reflection
    haveI : Fact q.Prime := ⟨hq⟩
    have hW : (((q - 1)! : ℕ) : ZMod q) = -1 := ZMod.wilsons_lemma q
    have hsplit : (q - 1 - k)! * (q - 1).descFactorial k = (q - 1)! :=
      Nat.factorial_mul_descFactorial (by omega)
    have hPk : q - 1 - k = P := by omega
    rw [hPk] at hsplit
    have hPf : ((P ! : ℕ) : ZMod q) = -1 := by
      have : ((P ! + 1 : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hqd
      push_cast at this; linear_combination this
    have hkf : ((k ! + 1 : ℕ) : ZMod q) = 0 := by
      have h1 := congrArg (fun n : ℕ => (n : ZMod q)) hsplit
      simp only [Nat.cast_mul] at h1
      rw [hPf, hW, e1074_desc q k (by omega) (by omega)] at h1
      have hneg : ((-1 : ZMod q)) ^ k = -1 := by
        rw [show k = 2 * (k / 2) + 1 by omega, pow_succ, pow_mul]; simp
      rw [hneg] at h1
      push_cast; linear_combination h1
    refine ⟨q, ⟨hq, k, by omega, ?_, (ZMod.natCast_eq_zero_iff _ _).mp hkf⟩, by omega⟩
    intro hk1
    have hkd : k ∣ q - 1 := (Nat.modEq_iff_dvd' (by omega)).mp hk1.symm
    have hkP : k ∣ P := by
      have : q - 1 = k + P := by omega
      rw [this] at hkd; exact (Nat.dvd_add_right (dvd_refl k)).mp hkd
    have hPk' : P ∣ k := by
      have : q - 1 = k + P := by omega
      rw [this] at hPd; exact (Nat.dvd_add_left (dvd_refl P)).mp hPd
    have hkeq : k = P := Nat.dvd_antisymm hkP hPk'
    have h3 : 3 ∣ q := by omega
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).mp h3
    omega
  · exact ⟨q, ⟨hq, P, by omega, hmod, hqd⟩, by omega⟩

/-- Erdős, Hardy, and Subbarao proved that $P$ is infinite. -/
@[category research solved, AMS 11]
theorem erdos_1074.variants.PillaiPrimes_infinite : PillaiPrimes.Infinite := by
  exact Set.infinite_of_forall_exists_gt e1074_big

/-- The sequence $S$ begins $8, 9, 13, 14, 15, 16, 17, ...$ -/
@[category test, AMS 11]
theorem erdos_1074.variants.EHSNumbers_init :
    nth EHSNumbers '' (Set.Icc 0 6) = {8, 9, 13, 14, 15, 16, 17} := by
  sorry

/-- The sequence $P$ begins $23, 29, 59, 61, 67, 71, ...$ -/
@[category test, AMS 11]
theorem erdos_1074.variants.PillaiPrimes_init :
    nth PillaiPrimes '' (Set.Icc 0 5) = {23, 29, 59, 61, 67, 71} := by
  sorry

/-- Regarding the first question, Hardy and Subbarao computed all EHS numbers up to $2^{10}$, and
write "...if this trend conditions we expect [the limit] to be around 0.5, if it exists. The
frequency with which the EHS numbers occur - most often in long sequences of consecutive integers -
makes us believe that their asymptotic density exists and is unity. Erdős, though initially
hesitant, later agreed with this view." That is, the conjecture is that $S$ has density $1$. -/
@[category research open, AMS 11]
theorem erdos_1074.variants.EHSNumbers_one : EHSNumbers.HasDensity 1 := by
  sorry

end Erdos1074
