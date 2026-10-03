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
# Conjectures associated with A063880

A063880 lists numbers $n$ such that $\sigma(n) = 2 \cdot \text{usigma}(n)$, where $\sigma(n)$ is the
sum of all divisors and $\text{usigma}(n)$ is the sum of unitary divisors.

Equivalently, these are numbers whose unitary and non-unitary divisors have equal sum.

The conjectures state that all members satisfy $n \equiv 108 \pmod{216}$, and that all
primitive terms (those whose proper divisors aren't in the sequence) are powerful numbers,
with $108$ being the only primitive term.

*References:*
- [A063880](https://oeis.org/A063880)
-/

@[expose] public section

namespace OeisA63880

open scoped ArithmeticFunction.sigma

/-- The set of unitary divisors of $n$: divisors $d$ such that $\gcd(d, n/d) = 1$. -/
def unitaryDivisors (n : ℕ) : Finset ℕ :=
  {d ∈ n.divisors | d.Coprime (n / d)}

/-- The sum of unitary divisors of $n$, denoted $\text{usigma}(n)$. -/
def usigma (n : ℕ) : ℕ :=
  ∑ d ∈ unitaryDivisors n, d

/-- A number $n$ is in the sequence A063880 if $\sigma(n) = 2 \cdot \text{usigma}(n)$. -/
def A (n : ℕ) : Prop :=
  0 < n ∧ σ 1 n = 2 * usigma n

/-- A term $n$ is primitive if no proper divisor of $n$ is in the sequence. -/
abbrev IsPrimitiveTerm (n : ℕ) : Prop := {n | A n}.IsPrimitive n

/-- $108$ is in the sequence A063880. -/
@[category test, AMS 11]
theorem a_108 : A 108 := by
  refine ⟨by norm_num, ?_⟩
  decide

/-- $540$ is in the sequence A063880. -/
@[category test, AMS 11]
theorem a_540 : A 540 := by
  refine ⟨by norm_num, ?_⟩
  decide

/-- $756$ is in the sequence A063880. -/
@[category test, AMS 11]
theorem a_756 : A 756 := by
  refine ⟨by norm_num, ?_⟩
  decide

/-- $108$ is a primitive term. -/
@[category test, AMS 11]
theorem isPrimitiveTerm_108 : IsPrimitiveTerm 108 := by
  rw [IsPrimitiveTerm, Set.isPrimitive_iff]
  refine ⟨a_108, ?_⟩
  intro d hd
  have ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.mp hd
  interval_cases d <;> simp_all [A] <;> decide

/-- All members of the sequence satisfy $n \equiv 108 \pmod{216}$. -/
@[category research open, AMS 11]
theorem mod_216_of_a {n : ℕ} (h : A n) : n % 216 = 108 := by
  sorry

/-- The unitary divisors of `m * p`, for a prime `p` not dividing `m > 0`, are the unitary
divisors of `m` and their multiples by `p`. -/
@[category API, AMS 11]
theorem unitaryDivisors_mul_prime {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m) :
    unitaryDivisors (m * p) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p) := by
  have hp0 : 0 < p := hp.pos
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).2 hpm
  ext d
  simp only [unitaryDivisors, Finset.mem_filter, Nat.mem_divisors, Finset.mem_union,
    Finset.mem_image]
  constructor
  · rintro ⟨⟨hd, -⟩, hcd⟩
    obtain ⟨d₁, d₂, hd₁, hd₂, rfl⟩ := dvd_mul.1 hd
    obtain ⟨t, rfl⟩ := hd₁
    have hd₁0 : 0 < d₁ := Nat.pos_of_mul_pos_right hm
    rcases (Nat.dvd_prime hp).1 hd₂ with h2 | h2 <;> subst d₂
    · -- `d = d₁` is a unitary divisor of `m`
      left
      rw [mul_one] at hcd ⊢
      have e : d₁ * t * p / d₁ = t * p := by
        rw [mul_assoc, Nat.mul_div_cancel_left _ hd₁0]
      rw [e] at hcd
      refine ⟨⟨dvd_mul_right d₁ t, hm.ne'⟩, ?_⟩
      rw [Nat.mul_div_cancel_left _ hd₁0]
      exact (Nat.coprime_mul_iff_right.1 hcd).1
    · -- `d = d₁ * p`
      right
      have e : d₁ * t * p / (d₁ * p) = t := by
        rw [mul_right_comm, Nat.mul_div_cancel_left _ (Nat.mul_pos hd₁0 hp0)]
      rw [e] at hcd
      refine ⟨d₁, ⟨⟨dvd_mul_right d₁ t, hm.ne'⟩, ?_⟩, rfl⟩
      rw [Nat.mul_div_cancel_left _ hd₁0]
      exact (Nat.coprime_mul_iff_left.1 hcd).1
  · rintro (⟨⟨hd, -⟩, hcd⟩ | ⟨d₁, ⟨⟨hd₁, -⟩, hcd⟩, rfl⟩)
    · obtain ⟨t, rfl⟩ := hd
      have hd0 : 0 < d := Nat.pos_of_mul_pos_right hm
      rw [Nat.mul_div_cancel_left _ hd0] at hcd
      refine ⟨⟨dvd_mul_of_dvd_left (dvd_mul_right d t) p, (Nat.mul_pos hm hp0).ne'⟩, ?_⟩
      rw [mul_assoc, Nat.mul_div_cancel_left _ hd0]
      refine Nat.Coprime.mul_right hcd ?_
      exact ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hpm (h.trans (dvd_mul_right d t))).symm
    · obtain ⟨t, rfl⟩ := hd₁
      have hd₁0 : 0 < d₁ := Nat.pos_of_mul_pos_right hm
      rw [Nat.mul_div_cancel_left _ hd₁0] at hcd
      refine ⟨⟨mul_dvd_mul (dvd_mul_right d₁ t) dvd_rfl, (Nat.mul_pos hm hp0).ne'⟩, ?_⟩
      rw [show d₁ * t * p / (d₁ * p) = t by
        rw [mul_right_comm, Nat.mul_div_cancel_left _ (Nat.mul_pos hd₁0 hp0)]]
      refine Nat.Coprime.mul_left hcd ?_
      exact (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hpm (h.trans (dvd_mul_left t d₁))

/-- `usigma` is multiplicative at a prime not dividing the argument. -/
@[category API, AMS 11]
theorem usigma_mul_prime {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m) :
    usigma (m * p) = usigma m * (p + 1) := by
  have hdisj : Disjoint (unitaryDivisors m) ((unitaryDivisors m).image (· * p)) := by
    rw [Finset.disjoint_left]
    intro d hd hd'
    obtain ⟨d₁, hd₁, rfl⟩ := Finset.mem_image.1 hd'
    have h1 : d₁ * p ∣ m := (Finset.mem_filter.1 hd).1 |> Nat.mem_divisors.1 |>.1
    exact hpm ((dvd_mul_left p d₁).trans h1)
  unfold usigma
  rw [unitaryDivisors_mul_prime hm hp hpm, Finset.sum_union hdisj,
    Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_right hp.pos h), ← Finset.sum_mul,
    mul_add, mul_one, add_comm]

/-- `σ` is multiplicative at a prime not dividing the argument. -/
@[category API, AMS 11]
theorem sigma_mul_prime {m p : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) :
    σ 1 (m * p) = σ 1 m * (p + 1) := by
  have hσp : σ 1 p = p + 1 := by
    have := ArithmeticFunction.sigma_one_apply_prime_pow hp (i := 1)
    simp [Finset.sum_range_succ] at this
    omega
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
    ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm).symm, hσp]

/-- Membership in the sequence is preserved by multiplying with a prime not dividing the term. -/
@[category API, AMS 11]
theorem A_mul_prime {m p : ℕ} (hA : A m) (hp : p.Prime) (hpm : ¬ p ∣ m) : A (m * p) :=
  ⟨Nat.mul_pos hA.1 hp.pos, by
    rw [sigma_mul_prime hp hpm, usigma_mul_prime hA.1 hp hpm, hA.2]; ring⟩

/-- Conversely, if `m * p` is in the sequence with `p` a prime not dividing `m > 0`, so is `m`. -/
@[category API, AMS 11]
theorem A_of_mul_prime {m p : ℕ} (hm : 0 < m) (hA : A (m * p)) (hp : p.Prime) (hpm : ¬ p ∣ m) :
    A m := by
  refine ⟨hm, ?_⟩
  have h := hA.2
  rw [sigma_mul_prime hp hpm, usigma_mul_prime hm hp hpm, ← mul_assoc] at h
  exact Nat.eq_of_mul_eq_mul_right (by omega) h

/-- Membership in the sequence is preserved by multiplying with a coprime squarefree number. -/
@[category API, AMS 11]
theorem A_mul_of_squarefree (s : ℕ) :
    ∀ m, A m → Squarefree s → m.Coprime s → A (m * s) := by
  induction s using Nat.recOnPrimeCoprime with
  | zero => intro m _ hs; exact absurd hs not_squarefree_zero
  | prime_pow p n hp =>
    intro m hA hs hcop
    have hn : n ≤ 1 := by
      by_contra hn
      exact absurd hs ((Nat.squarefree_pow_iff hp.ne_one (by omega)).not.2 (by omega))
    interval_cases n
    · simpa using hA
    · rw [pow_one] at hcop ⊢
      exact A_mul_prime hA hp ((Nat.Prime.coprime_iff_not_dvd hp).1 hcop.symm)
  | coprime a b _ _ hab iha ihb =>
    intro m hA hs hcop
    rw [← mul_assoc]
    exact ihb (m * a) (iha m hA hs.of_mul_left (Nat.Coprime.coprime_mul_right_right hcop))
      hs.of_mul_right (Nat.Coprime.mul_left (Nat.Coprime.coprime_mul_left_right hcop) hab)

/-- All primitive terms are powerful numbers: if `p` divided `n` exactly once, then `n / p` would
also be in the sequence. -/
@[category textbook, AMS 11]
theorem powerful_of_isPrimitiveTerm {n : ℕ} (h : IsPrimitiveTerm n) : n.Powerful := by
  intro p hp
  by_contra hp2
  have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hn : 0 < n := h.mem.1
  obtain ⟨m, rfl⟩ := hpn
  have hm : 0 < m := Nat.pos_of_mul_pos_left hn
  have hpm : ¬ p ∣ m := fun hd => hp2 (by rw [sq]; exact Nat.mul_dvd_mul_left p hd)
  have hAm : A m := A_of_mul_prime hm (by rw [mul_comm]; exact h.mem) hpp hpm
  exact h.not_mem_of_dvd_of_lt (dvd_mul_left m p)
    (by have := hpp.two_le; nlinarith) hAm

/-- $108$ is the only primitive term. -/
@[category research open, AMS 11]
theorem unique_primitive_108 {n : ℕ} (h : IsPrimitiveTerm n) : n = 108 := by
  sorry

/-- If $m$ is a primitive term and $s$ is squarefree with $\gcd(m, s) = 1$, then $m \cdot s$
is in the sequence. -/
@[category textbook, AMS 11]
theorem a_of_primitive_mul_squarefree (m s : ℕ) (hm : IsPrimitiveTerm m)
    (hs : Squarefree s) (hcoprime : m.Coprime s) : A (m * s) :=
  A_mul_of_squarefree s m hm.mem hs hcoprime

/-- Prime-power version of `unitaryDivisors_mul_prime`. -/
theorem a63_unitaryDivisors_mul_pow {m p f : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m)
    (hf : 1 ≤ f) :
    unitaryDivisors (m * p ^ f) =
      unitaryDivisors m ∪ (unitaryDivisors m).image (· * p ^ f) := by
  have hq0 : 0 < p ^ f := pow_pos hp.pos f
  have hcopq : ∀ x, ¬ p ∣ x → Nat.Coprime (p ^ f) x := fun x hx =>
    Nat.Coprime.pow_left f ((Nat.Prime.coprime_iff_not_dvd hp).2 hx)
  ext d
  simp only [unitaryDivisors, Finset.mem_filter, Nat.mem_divisors, Finset.mem_union,
    Finset.mem_image]
  constructor
  · rintro ⟨⟨hd, -⟩, hcd⟩
    obtain ⟨d₁, d₂, hd₁, hd₂, rfl⟩ := dvd_mul.1 hd
    obtain ⟨t, rfl⟩ := hd₁
    have hd₁0 : 0 < d₁ := Nat.pos_of_mul_pos_right hm
    obtain ⟨g, hg, rfl⟩ := (Nat.dvd_prime_pow hp).1 hd₂
    have hg0 : 0 < p ^ g := pow_pos hp.pos g
    have e : d₁ * t * p ^ f / (d₁ * p ^ g) = t * p ^ (f - g) := by
      rw [show p ^ f = p ^ g * p ^ (f - g) by rw [← pow_add]; congr 1; omega]
      rw [show d₁ * t * (p ^ g * p ^ (f - g)) = (d₁ * p ^ g) * (t * p ^ (f - g)) by ring,
        Nat.mul_div_cancel_left _ (Nat.mul_pos hd₁0 hg0)]
    rw [e] at hcd
    rcases Nat.eq_zero_or_pos g with rfl | hgpos
    · left
      simp only [pow_zero, mul_one, Nat.sub_zero] at hcd ⊢
      refine ⟨⟨dvd_mul_right d₁ t, hm.ne'⟩, ?_⟩
      rw [Nat.mul_div_cancel_left _ hd₁0]
      exact (Nat.coprime_mul_iff_right.1 hcd).1
    · rcases Nat.lt_or_ge g f with hgf | hgf
      · exfalso
        have h1 : p ∣ d₁ * p ^ g := dvd_mul_of_dvd_right (dvd_pow_self p hgpos.ne') _
        have h2 : p ∣ t * p ^ (f - g) := dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) _
        have := (Nat.Coprime.coprime_dvd_left h1 hcd).coprime_dvd_right h2
        rw [Nat.coprime_self] at this
        exact hp.one_lt.ne' this
      · right
        obtain rfl : g = f := le_antisymm hg hgf
        simp only [Nat.sub_self, pow_zero, mul_one] at hcd
        refine ⟨d₁, ⟨⟨dvd_mul_right d₁ t, hm.ne'⟩, ?_⟩, rfl⟩
        rw [Nat.mul_div_cancel_left _ hd₁0]
        exact (Nat.coprime_mul_iff_left.1 hcd).1
  · rintro (⟨⟨hd, -⟩, hcd⟩ | ⟨d₁, ⟨⟨hd₁, -⟩, hcd⟩, rfl⟩)
    · obtain ⟨t, rfl⟩ := hd
      have hd0 : 0 < d := Nat.pos_of_mul_pos_right hm
      rw [Nat.mul_div_cancel_left _ hd0] at hcd
      refine ⟨⟨dvd_mul_of_dvd_left (dvd_mul_right d t) _, (Nat.mul_pos hm hq0).ne'⟩, ?_⟩
      rw [mul_assoc, Nat.mul_div_cancel_left _ hd0]
      exact Nat.Coprime.mul_right hcd (hcopq d fun h => hpm (h.trans (dvd_mul_right d t))).symm
    · obtain ⟨t, rfl⟩ := hd₁
      have hd₁0 : 0 < d₁ := Nat.pos_of_mul_pos_right hm
      rw [Nat.mul_div_cancel_left _ hd₁0] at hcd
      refine ⟨⟨mul_dvd_mul (dvd_mul_right d₁ t) dvd_rfl, (Nat.mul_pos hm hq0).ne'⟩, ?_⟩
      rw [show d₁ * t * p ^ f / (d₁ * p ^ f) = t by
        rw [mul_right_comm, Nat.mul_div_cancel_left _ (Nat.mul_pos hd₁0 hq0)]]
      exact Nat.Coprime.mul_left hcd (hcopq t fun h => hpm (h.trans (dvd_mul_left t d₁)))

theorem a63_usigma_mul_pow {m p f : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m) (hf : 1 ≤ f) :
    usigma (m * p ^ f) = usigma m * (1 + p ^ f) := by
  have hq0 : 0 < p ^ f := pow_pos hp.pos f
  have hdisj : Disjoint (unitaryDivisors m) ((unitaryDivisors m).image (· * p ^ f)) := by
    rw [Finset.disjoint_left]
    intro d hd hd'
    obtain ⟨d₁, hd₁, rfl⟩ := Finset.mem_image.1 hd'
    have h1 : d₁ * p ^ f ∣ m := (Finset.mem_filter.1 hd).1 |> Nat.mem_divisors.1 |>.1
    exact hpm ((dvd_pow_self p (by omega)).trans ((dvd_mul_left _ d₁).trans h1))
  unfold usigma
  rw [a63_unitaryDivisors_mul_pow hm hp hpm hf, Finset.sum_union hdisj,
    Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_right hq0 h), ← Finset.sum_mul,
    mul_add, mul_one]

theorem a63_usigma_one : usigma 1 = 1 := by decide

theorem a63_usigma_pow {p g : ℕ} (hp : p.Prime) (hg : 1 ≤ g) : usigma (p ^ g) = 1 + p ^ g := by
  have := a63_usigma_mul_pow (m := 1) (by norm_num) hp (fun h => hp.one_lt.ne' (Nat.dvd_one.mp h)) hg
  rwa [one_mul, a63_usigma_one, one_mul] at this

theorem a63_geom {p k : ℕ} (hp : p.Prime) :
    ((σ 1 (p ^ k) : ℕ) : ℤ) * ((p : ℤ) - 1) = (p : ℤ) * (p : ℤ) ^ k - 1 := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  push_cast
  rw [geom_sum_mul, pow_succ]; ring

/-- Prime-power comparison of `σ / usigma`. -/
theorem a63_pp {p f g : ℕ} (hp : p.Prime) (hf : 2 ≤ f) (hg : g ≤ f) :
    σ 1 (p ^ g) * usigma (p ^ f) ≤ σ 1 (p ^ f) * usigma (p ^ g) ∧
      (σ 1 (p ^ g) * usigma (p ^ f) = σ 1 (p ^ f) * usigma (p ^ g) → g = f) := by
  have hP : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  have hf' := a63_geom (k := f) hp
  have hg' := a63_geom (k := g) hp
  have hUf : ((usigma (p ^ f) : ℕ) : ℤ) = 1 + (p : ℤ) ^ f := by
    rw [a63_usigma_pow hp (by omega)]; push_cast; ring
  have hAB : (p : ℤ) ^ g ≤ (p : ℤ) ^ f := pow_le_pow_right₀ (by linarith) hg
  suffices h : ((σ 1 (p ^ g) : ℕ) : ℤ) * (usigma (p ^ f) : ℕ) ≤
      ((σ 1 (p ^ f) : ℕ) : ℤ) * (usigma (p ^ g) : ℕ) ∧
      (((σ 1 (p ^ g) : ℕ) : ℤ) * (usigma (p ^ f) : ℕ) =
        ((σ 1 (p ^ f) : ℕ) : ℤ) * (usigma (p ^ g) : ℕ) → g = f) by
    refine ⟨by exact_mod_cast h.1, fun e => h.2 (by exact_mod_cast e)⟩
  rw [hUf]
  set SF : ℤ := ((σ 1 (p ^ f) : ℕ) : ℤ)
  set SG : ℤ := ((σ 1 (p ^ g) : ℕ) : ℤ)
  set B : ℤ := (p : ℤ) ^ f
  rcases Nat.eq_zero_or_pos g with rfl | hgpos
  · have hU0 : ((usigma (p ^ 0) : ℕ) : ℤ) = 1 := by rw [pow_zero, a63_usigma_one]; rfl
    rw [hU0]
    have hSG : SG = 1 := by
      have : (SG - 1) * ((p : ℤ) - 1) = 0 := by linear_combination hg'
      rcases mul_eq_zero.mp this with h | h <;> linarith
    have hB : (p : ℤ) ^ 2 ≤ B := pow_le_pow_right₀ (by linarith) hf
    have key : (SF - 1 - B) * ((p : ℤ) - 1) = B - p := by linear_combination hf'
    have hpos : 0 < SF - 1 - B := by
      by_contra h; push Not at h; nlinarith
    rw [hSG]
    exact ⟨by linarith, fun h => by exfalso; linarith⟩
  · have hUg : ((usigma (p ^ g) : ℕ) : ℤ) = 1 + (p : ℤ) ^ g := by
      rw [a63_usigma_pow hp hgpos]; push_cast; ring
    rw [hUg]
    set A : ℤ := (p : ℤ) ^ g
    have key : (SF * (1 + A) - SG * (1 + B)) * ((p : ℤ) - 1) = ((p : ℤ) + 1) * (B - A) := by
      linear_combination (1 + A) * hf' - (1 + B) * hg'
    constructor
    · by_contra h; push Not at h; nlinarith
    · intro h
      have hBA : B = A := by
        have : ((p : ℤ) + 1) * (B - A) = 0 := by rw [← key, h]; ring
        rcases mul_eq_zero.mp this with h0 | h0 <;> linarith
      by_contra hne
      have : A < B := pow_lt_pow_right₀ (by linarith) (lt_of_le_of_ne hg hne)
      linarith

theorem a63_usigma_pos {x : ℕ} (hx : 0 < x) : 0 < usigma x := by
  unfold usigma
  have h1 : 1 ∈ unitaryDivisors x := by
    simp [unitaryDivisors, Nat.mem_divisors, hx.ne']
  exact lt_of_lt_of_le Nat.one_pos (Finset.single_le_sum (f := fun d => d) (fun _ _ => Nat.zero_le _) h1)

/-- `usigma (x * p ^ g) = usigma x * usigma (p ^ g)` for `p ∤ x`, including `g = 0`. -/
theorem a63_usigma_split {x p g : ℕ} (hx : 0 < x) (hp : p.Prime) (hpx : ¬ p ∣ x) :
    usigma (x * p ^ g) = usigma x * usigma (p ^ g) := by
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · simp [a63_usigma_one]
  · rw [a63_usigma_mul_pow hx hp hpx hg, a63_usigma_pow hp hg]

theorem a63_sigma_split {x p g : ℕ} (hp : p.Prime) (hpx : ¬ p ∣ x) :
    σ 1 (x * p ^ g) = σ 1 x * σ 1 (p ^ g) :=
  ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
    (Nat.Coprime.pow_right g ((Nat.Prime.coprime_iff_not_dvd hp).2 hpx).symm)

/-- For powerful `m` and `d ∣ m`: `σ(d)/u(d) ≤ σ(m)/u(m)`, with equality only for `d = m`. -/
theorem a63_ratio : ∀ m, 0 < m → Nat.Powerful m → ∀ d, d ∣ m →
    σ 1 d * usigma m ≤ σ 1 m * usigma d ∧
      (σ 1 d * usigma m = σ 1 m * usigma d → d = m) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hm hpow d hd
  rcases Nat.lt_or_ge m 2 with hm1 | hm1
  · obtain rfl : m = 1 := by omega
    obtain rfl : d = 1 := Nat.dvd_one.mp hd
    exact ⟨le_rfl, fun _ => rfl⟩
  set p := m.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpm : p ∣ m := Nat.minFac_dvd m
  have hm0 : m ≠ 0 := by omega
  set f := m.factorization p with hfdef
  have hf2 : 2 ≤ f :=
    (hp.pow_dvd_iff_le_factorization hm0).mp (hpow p (Nat.mem_primeFactors.mpr ⟨hp, hpm, hm0⟩))
  set m' := m / p ^ f with hm'def
  have hmm : m = m' * p ^ f := by rw [mul_comm]; exact (Nat.ordProj_mul_ordCompl_eq_self m p).symm
  have hpm' : ¬ p ∣ m' := Nat.not_dvd_ordCompl hp hm0
  have hm'0 : 0 < m' := Nat.pos_of_ne_zero (fun h => by rw [h, zero_mul] at hmm; omega)
  have hpf : 4 ≤ p ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hp.two_le 2
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf2
  have hm'lt : m' < m := by rw [hmm]; nlinarith
  have hcop : ∀ x, x ∣ m → ¬ p ∣ x → x ∣ m' := by
    intro x hx hpx
    rw [hmm] at hx
    exact (Nat.Coprime.pow_right f ((Nat.Prime.coprime_iff_not_dvd hp).2 hpx).symm).dvd_of_dvd_mul_right hx
  have hpow' : Nat.Powerful m' := by
    intro q hq
    obtain ⟨hqp, hqm', -⟩ := Nat.mem_primeFactors.mp hq
    have hqm : q ∣ m := hqm'.trans ⟨p ^ f, hmm⟩
    have hq2 := hpow q (Nat.mem_primeFactors.mpr ⟨hqp, hqm, hm0⟩)
    refine hcop _ hq2 (fun h => hpm' ?_)
    have : p ∣ q := hp.dvd_of_dvd_pow h
    rw [(Nat.prime_dvd_prime_iff_eq hp hqp).mp this]; exact hqm'
  -- decompose d
  have hd0 : d ≠ 0 := fun h => by rw [h, zero_dvd_iff] at hd; omega
  set g := d.factorization p with hgdef
  set d' := d / p ^ g with hd'def
  have hdd : d = d' * p ^ g := by rw [mul_comm]; exact (Nat.ordProj_mul_ordCompl_eq_self d p).symm
  have hpd' : ¬ p ∣ d' := Nat.not_dvd_ordCompl hp hd0
  have hd'0 : 0 < d' := Nat.pos_of_ne_zero (fun h => by rw [h, zero_mul] at hdd; exact hd0 hdd)
  have hgf : g ≤ f := (Nat.factorization_le_iff_dvd hd0 hm0).mpr hd p
  have hd'm' : d' ∣ m' := hcop d' ((Dvd.intro _ hdd.symm).trans hd) hpd'
  obtain ⟨ib, ie⟩ := ih m' hm'lt hm'0 hpow' d' hd'm'
  obtain ⟨pb, pe⟩ := a63_pp hp hf2 hgf
  have eL : σ 1 d * usigma m = (σ 1 (p ^ g) * usigma (p ^ f)) * (σ 1 d' * usigma m') := by
    rw [hdd, hmm, a63_sigma_split hp hpd', a63_usigma_split hm'0 hp hpm']; ring
  have eR : σ 1 m * usigma d = (σ 1 (p ^ f) * usigma (p ^ g)) * (σ 1 m' * usigma d') := by
    rw [hdd, hmm, a63_sigma_split hp hpm', a63_usigma_split hd'0 hp hpd']; ring
  have ha : 0 < σ 1 (p ^ g) * usigma (p ^ f) :=
    Nat.mul_pos (ArithmeticFunction.sigma_pos 1 _ (pow_pos hp.pos g).ne')
      (a63_usigma_pos (pow_pos hp.pos f))
  have hb : 0 < σ 1 d' * usigma m' :=
    Nat.mul_pos (ArithmeticFunction.sigma_pos 1 _ hd'0.ne') (a63_usigma_pos hm'0)
  rw [eL, eR]
  refine ⟨Nat.mul_le_mul pb ib, fun h => ?_⟩
  have h1 : σ 1 (p ^ g) * usigma (p ^ f) = σ 1 (p ^ f) * usigma (p ^ g) := by
    by_contra hne
    have := lt_of_le_of_ne pb hne
    have : (σ 1 (p ^ g) * usigma (p ^ f)) * (σ 1 d' * usigma m') <
        (σ 1 (p ^ f) * usigma (p ^ g)) * (σ 1 m' * usigma d') :=
      Nat.mul_lt_mul_of_lt_of_le this ib
        (Nat.mul_pos (ArithmeticFunction.sigma_pos 1 _ hm'0.ne') (a63_usigma_pos hd'0))
    omega
  have h2 : σ 1 d' * usigma m' = σ 1 m' * usigma d' := by
    rw [h1] at h
    exact Nat.eq_of_mul_eq_mul_left (by rw [← h1]; exact ha) h
  rw [hdd, hmm, ie h2, pe h1]

theorem a63_primitive_of_powerful {m : ℕ} (hA : A m) (hpow : Nat.Powerful m) :
    IsPrimitiveTerm m := by
  rw [IsPrimitiveTerm, Set.isPrimitive_iff]
  refine ⟨hA, fun d hd hAd => ?_⟩
  obtain ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.mp hd
  have hAd' : A d := hAd
  have := (a63_ratio m hA.1 hpow d hdvd).2 (by rw [hAd'.2, hA.2]; ring)
  omega

theorem a63_strip : ∀ n, A n → ∃ m s, A m ∧ Nat.Powerful m ∧ Squarefree s ∧ m.Coprime s ∧
    n = m * s := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hA
  by_cases hpow : Nat.Powerful n
  · exact ⟨n, 1, hA, hpow, squarefree_one, Nat.coprime_one_right n, by ring⟩
  · have hn0 : n ≠ 0 := hA.1.ne'
    simp only [Nat.Powerful, Nat.Full, not_forall] at hpow
    obtain ⟨p, hp, hp2⟩ := hpow
    obtain ⟨hpp, hpn, -⟩ := Nat.mem_primeFactors.mp hp
    obtain ⟨n', hn'⟩ := hpn
    have hn'0 : 0 < n' := Nat.pos_of_ne_zero (fun h => by rw [h, mul_zero] at hn'; exact hn0 hn')
    have hpn' : ¬ p ∣ n' := fun h => hp2 (by rw [hn', sq]; exact Nat.mul_dvd_mul_left p h)
    have hAn' : A n' := A_of_mul_prime hn'0 (by rw [mul_comm, ← hn']; exact hA) hpp hpn'
    have hlt : n' < n := by rw [hn']; have := hpp.two_le; nlinarith
    obtain ⟨m, s', hAm, hpm, hs', hms', hn'eq⟩ := ih n' hlt hAn'
    have hps' : ¬ p ∣ s' := fun h => hpn' (h.trans (Dvd.intro_left m hn'eq.symm))
    have hpm' : ¬ p ∣ m := fun h => hpn' (h.trans (Dvd.intro s' hn'eq.symm))
    refine ⟨m, s' * p, hAm, hpm, ?_, ?_, ?_⟩
    · rw [Nat.squarefree_mul_iff]
      exact ⟨((Nat.Prime.coprime_iff_not_dvd hpp).2 hps').symm, hs', hpp.prime.squarefree⟩
    · exact Nat.Coprime.mul_right hms' ((Nat.Prime.coprime_iff_not_dvd hpp).2 hpm').symm
    · rw [hn', hn'eq]; ring

/-- Non-primitive terms have the form $m \cdot s$ where $m$ is primitive and $s$ is
squarefree with $\gcd(m, s) = 1$. -/
@[category research solved, AMS 11]
theorem exists_primitive_of_a {n : ℕ} (h : A n) :
    ∃ m s, IsPrimitiveTerm m ∧ Squarefree s ∧ m.Coprime s ∧ n = m * s := by
  obtain ⟨m, s, hAm, hpow, hs, hcop, rfl⟩ := a63_strip n h
  exact ⟨m, s, a63_primitive_of_powerful hAm hpow, hs, hcop, rfl⟩

end OeisA63880
