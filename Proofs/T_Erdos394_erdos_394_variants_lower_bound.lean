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
# Erdős Problem 394

*References:*
- [erdosproblems.com/394](https://www.erdosproblems.com/394)
- [ErGr80] Erdős, P. and Graham, R., Old and new problems and results in combinatorial number
  theory. Monographies de L'Enseignement Mathematique (1980).
- [ErHa78] Erdős, P. and Hall, R. R., On some unconventional problems on the divisors of integers.
  J. Austral. Math. Soc. Ser. A (1978), 479--485.
-/

@[expose] public section

open Nat Filter Finset
open scoped Asymptotics Topology Nat

namespace Erdos394

/--
Let $t_k(n)$ denote the least $m$ such that $n\mid m(m+1)(m+2)\cdots (m+k-1).$
-/
noncomputable def t (k n : ℕ) : ℕ :=
  sInf { m : ℕ | 0 < m ∧ n ∣ ∏ i ∈ range k, (m + i) }

/-- `t k n = v` when `v` works and nothing positive below it does. -/
@[category API, AMS 11]
theorem t_eq_of {n k v : ℕ} (hv : 0 < v)
    (hdvd : n ∣ ∏ i ∈ range k, (v + i))
    (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) :
    t k n = v := by
  refine le_antisymm (Nat.sInf_le ⟨hv, hdvd⟩) ?_
  by_contra! hc
  have hne : { m : ℕ | 0 < m ∧ n ∣ ∏ i ∈ range k, (m + i) }.Nonempty := ⟨v, hv, hdvd⟩
  obtain ⟨hpos, hd⟩ := Nat.sInf_mem hne
  exact hlt _ (mem_range.mpr hc) hpos hd

/-- The least positive multiple of `n` is `n`, so `t 1 n = n`. -/
@[category API, AMS 11]
theorem t_one {n : ℕ} (hn : 0 < n) : t 1 n = n := by
  refine le_antisymm (Nat.sInf_le ⟨hn, by simp⟩) ?_
  have hne : { m : ℕ | 0 < m ∧ n ∣ ∏ i ∈ range 1, (m + i) }.Nonempty := ⟨n, hn, by simp⟩
  obtain ⟨hpos, hd⟩ := Nat.sInf_mem hne
  rw [prod_range_one, add_zero] at hd
  exact Nat.le_of_dvd hpos hd

/--
Is it true that $\sum_{n\leq x}t_2(n)\ll \frac{x^2}{(\log x)^c}$ for some $c>0$?
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/williamjblair/lean-proofs/blob/4f915a323443bfb1709a6805a013812016dca88a/starfleet/erdos-394/Research/FirstQuestion.lean"]
theorem erdos_394.parts.i :
    answer(True) ↔
      ∃ c > (0 : ℝ), (fun x ↦ ∑ n ∈ Icc 1 ⌊x⌋₊,
      (t 2 n : ℝ)) ≪ (fun x ↦ x ^ 2 / (Real.log x) ^ c) := by
  sorry

/--
Is it true that, for $k\geq 2$, $\sum_{n\leq x}t_{k+1}(n) =o\left(\sum_{n\leq x}t_k(n)\right)?$
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/williamjblair/lean-proofs/blob/4f915a323443bfb1709a6805a013812016dca88a/starfleet/erdos-394/Research/DenseHierarchyLittleO.lean"]
theorem erdos_394.parts.ii :
    answer(True) ↔
      ∀ k ≥ 2, (fun (x : ℝ) ↦ ∑ n ∈ Icc 1 ⌊x⌋₊,
      (t (k + 1) n : ℝ)) =o[atTop]
      (fun (x : ℝ) ↦ ∑ n ∈ Icc 1 ⌊x⌋₊,
      (t k n : ℝ)) := by
  sorry

/--
In [ErGr80] they mention a conjecture of Erdős that the sum is $o(x^2)$. This was proved by Erdős
and Hall [ErHa78], who proved that in fact
$\sum_{n\leq x}t_2(n)\ll \frac{\log\log\log x}{\log\log x}x^2.$
-/
@[category research solved, AMS 11]
theorem erdos_394.variants.hall_bound :
    (fun x ↦ ∑ n ∈ Icc 1 ⌊x⌋₊, (t 2 n : ℝ)) ≪
    (fun x ↦ x ^ 2 * (Real.log (Real.log (Real.log x)) / Real.log (Real.log x))) := by
  sorry

/--
Erdős and Hall conjecture that the sum is $o(x^2/(\log x)^c)$ for any $c<\log 2$.
-/
@[category research open, AMS 11]
theorem erdos_394.variants.hall_conjecture :
    ∀ c < Real.log 2, (fun x ↦ ∑ n ∈ Icc 1 ⌊x⌋₊,
    (t 2 n : ℝ)) =o[atTop]
    (fun x ↦ x ^ 2 / (Real.log x) ^ c) := by
  sorry

open Asymptotics Chebyshev in
lemma e394_t_prime (p : ℕ) (hp : p.Prime) : t 2 p = p - 1 := by
  have hp2 := hp.two_le
  apply t_eq_of (by omega)
  · rw [prod_range_succ, prod_range_one, add_zero, Nat.sub_add_cancel (by omega)]
    exact Dvd.intro_left _ rfl
  · intro m hm hm0
    rw [mem_range] at hm
    rw [prod_range_succ, prod_range_one, add_zero]
    intro hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
    · have := Nat.le_of_dvd hm0 h; omega
    · have := Nat.le_of_dvd (by omega) h; omega

open Asymptotics Chebyshev in
/-- Error terms of Chebyshev's lower bound are `o(n)`. -/
lemma e394_err : ∀ᶠ n : ℕ in atTop,
    Real.log ((n : ℝ) + 1) + 2 * √(n : ℝ) * Real.log n ≤ (1 / 32) * n := by
  have h1 : (fun x : ℝ => Real.log x) =o[atTop] (fun x => x ^ (1 / 2 : ℝ)) :=
    isLittleO_log_rpow_atTop (by norm_num)
  have h2 : (fun x : ℝ => √x * Real.log x) =o[atTop] (fun x : ℝ => x) := by
    have := (isBigO_refl (fun x : ℝ => √x) atTop).mul_isLittleO h1
    refine this.congr' (Eventually.of_forall fun x => rfl) ?_
    filter_upwards [eventually_ge_atTop 0] with x hx
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add' hx (by norm_num)]; norm_num
  have h3 : (fun x : ℝ => Real.log (x + 1)) =o[atTop] (fun x : ℝ => x) := by
    have hl : (fun x : ℝ => Real.log x) =o[atTop] (fun x : ℝ => x) := Real.isLittleO_log_id_atTop
    have hshift : (fun x : ℝ => Real.log (x + 1)) =O[atTop] (fun x : ℝ => Real.log x + 1) := by
      refine IsBigO.of_bound 1 ?_
      filter_upwards [eventually_ge_atTop 1] with x hx
      have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
      have h1 : Real.log (x + 1) ≤ Real.log (2 * x) := Real.log_le_log (by linarith) (by linarith)
      rw [Real.log_mul (by norm_num) (by linarith)] at h1
      have h2 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
      have h0 : 0 ≤ Real.log (x + 1) := Real.log_nonneg (by linarith)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0, abs_of_nonneg (by linarith)]
      linarith
    refine hshift.trans_isLittleO (hl.add ?_)
    exact (isLittleO_const_id_atTop (1 : ℝ))
  have h4 : (fun x : ℝ => Real.log (x + 1) + 2 * (√x * Real.log x)) =o[atTop] (fun x : ℝ => x) :=
    h3.add (h2.const_mul_left 2)
  have h5 := (h4.comp_tendsto tendsto_natCast_atTop_atTop).def (show (0 : ℝ) < 1 / 32 by norm_num)
  filter_upwards [h5, eventually_ge_atTop 1] with n hn hn1
  simp only [Function.comp, Real.norm_eq_abs] at hn
  have hpos : 0 ≤ Real.log ((n : ℝ) + 1) + 2 * (√(n : ℝ) * Real.log n) := by
    have : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
    have : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith [show (1:ℝ) ≤ n by exact_mod_cast hn1])
    positivity
  rw [abs_of_nonneg hpos, abs_of_nonneg (by positivity)] at hn
  linarith

open Asymptotics Chebyshev in
lemma e394_main_bound : ∀ᶠ n : ℕ in atTop,
    (n : ℝ) ^ 2 / Real.log n ≤ 36 * ∑ m ∈ Icc 1 n, (t 2 m : ℝ) := by
  filter_upwards [e394_err, eventually_ge_atTop 6] with n herr hn6
  have hn : (6 : ℝ) ≤ n := by exact_mod_cast hn6
  have hlogpos : 0 < Real.log n := Real.log_pos (by linarith)
  set q := ⌊(n : ℝ) / 3⌋₊ with hq
  have hqn : q ≤ n := by
    rw [hq]; apply Nat.floor_le_of_le; linarith
  set R := n.primesLE \ q.primesLE
  -- θ(n) − θ(n/3) ≤ #R · log n
  have hsub : q.primesLE ⊆ n.primesLE := by
    intro p hp; rw [Nat.mem_primesLE] at hp ⊢; exact ⟨hp.1.trans hqn, hp.2⟩
  have hθ : θ (n : ℝ) - θ ((n : ℝ) / 3) ≤ (#R : ℝ) * Real.log n := by
    rw [theta_eq_sum_primesLE, theta_eq_sum_primesLE, Nat.floor_natCast, ← hq,
      ← sum_sdiff hsub, add_sub_cancel_right]
    calc ∑ p ∈ R, Real.log p ≤ ∑ _p ∈ R, Real.log n := sum_le_sum fun p hp => by
          have hpn := (Nat.mem_primesLE.mp (mem_sdiff.mp hp).1)
          exact Real.log_le_log (by exact_mod_cast hpn.2.pos) (by exact_mod_cast hpn.1)
      _ = (#R : ℝ) * Real.log n := by rw [sum_const, nsmul_eq_mul]
  have hlow := theta_ge n
  have hup := theta_le_log4_mul_x (show (0 : ℝ) ≤ (n : ℝ) / 3 by positivity)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hl2 := Real.log_two_gt_d9
  have hR : (n : ℝ) / 6 ≤ (#R : ℝ) * Real.log n := by
    rw [hlog4] at hup
    nlinarith
  -- each prime in `R` contributes at least `n / 6`
  have hRsub : R ⊆ Icc 1 n := by
    intro p hp
    have := Nat.mem_primesLE.mp (mem_sdiff.mp hp).1
    rw [mem_Icc]; exact ⟨this.2.one_le, this.1⟩
  have hbig : ∀ p ∈ R, (n : ℝ) / 6 ≤ (t 2 p : ℝ) := by
    intro p hp
    obtain ⟨hpP, hpQ⟩ := mem_sdiff.mp hp
    have hpr := (Nat.mem_primesLE.mp hpP).2
    have hpq : q < p := by
      by_contra h; push Not at h; exact hpQ (Nat.mem_primesLE.mpr ⟨h, hpr⟩)
    have h1 : (n : ℝ) / 3 < p := by
      have := Nat.lt_floor_add_one ((n : ℝ) / 3)
      have : ((q + 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast hpq
      push_cast at this; linarith
    rw [e394_t_prime p hpr, Nat.cast_sub hpr.one_le]
    push_cast; linarith
  have hsum : (#R : ℝ) * ((n : ℝ) / 6) ≤ ∑ m ∈ Icc 1 n, (t 2 m : ℝ) := by
    calc (#R : ℝ) * ((n : ℝ) / 6) = ∑ _p ∈ R, (n : ℝ) / 6 := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ p ∈ R, (t 2 p : ℝ) := sum_le_sum hbig
      _ ≤ ∑ m ∈ Icc 1 n, (t 2 m : ℝ) :=
          sum_le_sum_of_subset_of_nonneg hRsub fun _ _ _ => by positivity
  rw [div_le_iff₀ hlogpos]
  have : (n : ℝ) ^ 2 ≤ 36 * ((#R : ℝ) * Real.log n) * ((n : ℝ) / 6) := by nlinarith
  nlinarith

open Asymptotics Chebyshev in
theorem e394_main : (fun x : ℕ ↦ (x : ℝ) ^ 2 / Real.log x) =O[atTop]
    (fun x : ℕ ↦ ∑ n ∈ Icc 1 ⌊(x : ℕ)⌋₊, (t 2 n : ℝ)) := by
  refine IsBigO.of_bound 36 ?_
  filter_upwards [e394_main_bound, eventually_ge_atTop 2] with n hn hn2
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn2)
  have hf : ⌊n⌋₊ = n := by simp
  rw [hf, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity),
    abs_of_nonneg (by positivity)]
  exact hn

/--
Since $t_2(p)=p-1$ for prime $p$ it is trivial that $\sum_{n\leq x}t_2(n)\gg \frac{x^2}{\log x}$.
-/
@[category research solved, AMS 11]
theorem erdos_394.variants.lower_bound :
    (fun x ↦ x ^ 2 / Real.log x) ≪
    (fun x ↦ ∑ n ∈ Icc 1 ⌊x⌋₊, (t 2 n : ℝ)) := by
  exact e394_main

/--
They ask about the behaviour of $t_{n-3}(n!)$ and also ask whether, for infinitely many $n$,
$t_k(n!)< t_{k-1}(n!)-1$ for all $1\leq k < n$.
-/
@[category research open, AMS 11]
theorem erdos_394.variants.factorial_gap_conjecture :
    answer(sorry) ↔
      Set.Infinite { n : ℕ | ∀ k, 2 ≤ k → k < n →
      t k (n !) < t (k - 1) (n !) - 1 } := by
  sorry

set_option maxRecDepth 20000 in
/--
They proved (with Selfridge) that this holds for $n=10$.
-/
@[category research solved, AMS 11]
theorem erdos_394.variants.factorial_gap_10 :
    ∀ (k : ℕ), 2 ≤ k → k < 10 →
    t k (10 !) <
    t (k - 1) (10 !) - 1 := by
  have h1 : t 1 (10 !) = 3628800 := by rw [t_one] <;> norm_num [Nat.factorial]
  have h2 : t 2 (10 !) = 512000 := by
    norm_num [Nat.factorial]; exact t_eq_of (by norm_num) (by native_decide) (by native_decide)
  have h3 : t 3 (10 !) = 6398 := by
    norm_num [Nat.factorial]; exact t_eq_of (by norm_num) (by native_decide) (by native_decide)
  have h4 : t 4 (10 !) = 5373 := by
    norm_num [Nat.factorial]; exact t_eq_of (by norm_num) (by native_decide) (by native_decide)
  have h5 : t 5 (10 !) = 348 := by
    norm_num [Nat.factorial]; exact t_eq_of (by norm_num) (by decide) (by decide)
  have h6 : t 6 (10 !) = 160 := by
    norm_num [Nat.factorial]; exact t_eq_of (by norm_num) (by decide) (by decide)
  have h7 : t 7 (10 !) = 30 := by
    norm_num [Nat.factorial]; exact t_eq_of (by norm_num) (by decide) (by decide)
  have h8 : t 8 (10 !) = 9 := by
    norm_num [Nat.factorial]; exact t_eq_of (by norm_num) (by decide) (by decide)
  have h9 : t 9 (10 !) = 2 := by
    norm_num [Nat.factorial]; exact t_eq_of (by norm_num) (by decide) (by decide)
  intro k hk2 hk10
  interval_cases k <;> simp_all

end Erdos394
