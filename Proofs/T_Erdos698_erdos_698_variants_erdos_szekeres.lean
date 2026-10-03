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
# Erdős Problem 698

*References:*
- [erdosproblems.com/698](https://www.erdosproblems.com/698)
- [ErSz78] Erdős, P. and Szekeres, G., *Some number theoretic problems on binomial
  coefficients*. Austral. Math. Soc. Gaz. (1978), 97-99.
- [Be11] Bergman, George M., *On common divisors of multinomial coefficients*. Bull. Aust.
  Math. Soc. (2011), 138--157.
-/

@[expose] public section

namespace Erdos698

open Filter

/--
Is there some $h(n)\to \infty$ such that for all $2\leq i<j\leq n/2$
$$\textrm{gcd}\left( \binom{n}{i},\binom{n}{j}\right) \geq h(n)?$$

This was resolved by Bergman [Be11], who proved that for any $2\leq i<j\leq n/2$
$$\textrm{gcd}\left( \binom{n}{i},\binom{n}{j}\right) \gg n^{1/2}\frac{2^i}{i^{3/2}},$$
where the implied constant is absolute.

The linked formal proof (van Doorn and Aristotle, see `erdos_698.variants.bergman`) gives the
explicit bound $\gcd > \frac{2^i \sqrt n}{4 i \sqrt{i - 1}}$, so $h(n) = \lfloor \sqrt n / 4 \rfloor$
works since $i \sqrt{i - 1} \le 2^i$ for $i \ge 2$.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos698.lean#L452"]
theorem erdos_698 : answer(True) ↔
    ∃ h : ℕ → ℕ, Tendsto h atTop atTop ∧
      ∀ n i j : ℕ, 2 ≤ i → i < j → j ≤ n / 2 →
        h n ≤ Nat.gcd (n.choose i) (n.choose j) := by
  sorry

lemma e698_desc (n j : ℕ) (hj : 2 * j ≤ n) : ∀ i, i ≤ j →
    2 ^ i * j.descFactorial i ≤ n.descFactorial i := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    intro hi
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ, pow_succ]
    have h1 := ih (by omega)
    have h2 : 2 * (j - i) ≤ n - i := by omega
    calc 2 ^ i * 2 * ((j - i) * j.descFactorial i)
        = (2 * (j - i)) * (2 ^ i * j.descFactorial i) := by ring
      _ ≤ (n - i) * n.descFactorial i := Nat.mul_le_mul h2 h1

/--
A problem of Erdős and Szekeres, who observed that
$$\textrm{gcd}\left( \binom{n}{i},\binom{n}{j}\right) \geq \frac{\binom{n}{i}}{\binom{j}{i}}
\geq 2^i$$
(in particular the greatest common divisor is always $>1$).
-/
@[category research solved, AMS 5 11]
theorem erdos_698.variants.erdos_szekeres (n i j : ℕ) (hi : 1 ≤ i) (hij : i < j)
    (hj : j ≤ n / 2) :
    (n.choose i : ℝ) / (j.choose i : ℝ) ≤ (Nat.gcd (n.choose i) (n.choose j) : ℝ) ∧
      (2 : ℝ) ^ i ≤ (n.choose i : ℝ) / (j.choose i : ℝ) := by
  have hjn : j ≤ n := by omega
  have hc : 0 < j.choose i := Nat.choose_pos hij.le
  have hcR : (0 : ℝ) < j.choose i := by exact_mod_cast hc
  constructor
  · -- C(n,i) ∣ C(n,j) * C(j,i)
    set a := n.choose i
    set b := n.choose j
    set c := j.choose i
    have hdiv : a ∣ b * c := ⟨(n - i).choose (j - i), Nat.choose_mul (n := n) (k := j) (s := i) hij.le⟩
    have h3 : a ≤ Nat.gcd a b * c :=
      Nat.le_of_dvd (Nat.mul_pos (Nat.gcd_pos_of_pos_left _ (Nat.choose_pos (by omega))) hc)
        (dvd_gcd_mul_of_dvd_mul hdiv)
    rw [div_le_iff₀ hcR]
    exact_mod_cast h3
  · have hd := e698_desc n j (by omega) i hij.le
    rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose] at hd
    have hf : 0 < i.factorial := Nat.factorial_pos i
    have h4 : 2 ^ i * j.choose i ≤ n.choose i := by
      have : i.factorial * (2 ^ i * j.choose i) ≤ i.factorial * n.choose i := by
        calc i.factorial * (2 ^ i * j.choose i) = 2 ^ i * (i.factorial * j.choose i) := by ring
          _ ≤ _ := hd
      exact Nat.le_of_mul_le_mul_left this hf
    rw [le_div_iff₀ hcR]
    exact_mod_cast h4

/--
This inequality is sharp for $i=1$, $j=p$, and $n=2p$.
-/
@[category research solved, AMS 5 11]
theorem erdos_698.variants.erdos_szekeres_sharp (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) :
    (Nat.gcd ((2 * p).choose 1) ((2 * p).choose p) : ℝ) =
        ((2 * p).choose 1 : ℝ) / (p.choose 1 : ℝ) ∧
      ((2 * p).choose 1 : ℝ) / (p.choose 1 : ℝ) = (2 : ℝ) ^ 1 := by
  sorry

/--
This was resolved by Bergman [Be11], who proved that for any $2\leq i<j\leq n/2$
$$\textrm{gcd}\left( \binom{n}{i},\binom{n}{j}\right) \gg n^{1/2}\frac{2^i}{i^{3/2}},$$
where the implied constant is absolute.
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos698.lean"]
theorem erdos_698.variants.bergman :
    ∃ c : ℝ, 0 < c ∧ ∀ n i j : ℕ, 2 ≤ i → i < j → j ≤ n / 2 →
      c * (Real.sqrt (n : ℝ) * (2 : ℝ) ^ i / ((i : ℝ) * Real.sqrt (i : ℝ))) ≤
        (Nat.gcd (n.choose i) (n.choose j) : ℝ) := by
  sorry

end Erdos698
