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
# Erdős Problem 302

*References:*
- [erdosproblems.com/302](https://www.erdosproblems.com/302)
- [BrRo91] Brown, Tom C. and Rödl, Voijtech, Monochromatic solutions to equations with unit
  fractions. Bull. Austral. Math. Soc. (1991), 387-392.
- [ErGr80] Erdős, P. and Graham, R., Old and new problems and results in combinatorial number
  theory. Monographies de L'Enseignement Mathematique (1980).
- [va25](https://github.com/Woett/Mathematical-shorts/blob/main/Two-colouring%20and%20density%20lead%20to%20solutions%20to%20an%20equation%20in%20unit%20fractions.pdf)
-/

@[expose] public section

open Filter Finset
open scoped Topology

namespace Erdos302

/--
A finite set $A$ of positive integers admits no solution to
$\frac{1}{a} = \frac{1}{b} + \frac{1}{c}$ with $a, b, c$ distinct elements of $A$.
-/
def NoUnitFractionTriple (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b → a ≠ c → b ≠ c →
    (1 : ℚ) / a ≠ (1 : ℚ) / b + (1 : ℚ) / c

/--
$f N$ is the size of the largest $A ⊆ \{1, …, N\}$ containing no solution to
$\frac{1}{a} = \frac{1}{b} + \frac{1}{c}$ with distinct $a, b, c ∈ A$.
-/
def IsMaxNoTripleCard (N m : ℕ) : Prop :=
  IsGreatest {k | ∃ A ⊆ Finset.Icc 1 N, NoUnitFractionTriple A ∧ A.card = k} m

/--
Let $f(N)$ be the size of the largest $A\subseteq \{1,\ldots,N\}$ such that there are no
solutions to
$$\frac{1}{a}= \frac{1}{b}+\frac{1}{c}$$
with distinct $a,b,c\in A$? Estimate $f(N)$.

The colouring version of this is [303], which was solved by Brown and Rödl [BrRo91].
-/
@[category research open, AMS 11]
theorem erdos_302.parts.i (f : ℕ → ℕ) (hf : ∀ N, IsMaxNoTripleCard N (f N)) :
    Tendsto (fun N : ℕ => (f N : ℝ) / N) atTop (𝓝 answer(sorry)) := by
  sorry

/--
In particular, is $f(N)=(\tfrac{1}{2}+o(1))N$?

This is false: it is contradicted by Cambie's lower bound of $(5/8+o(1))N$ recorded below,
since $5/8 > 1/2$.
-/
@[category research solved, AMS 11]
theorem erdos_302.parts.ii (f : ℕ → ℕ) (hf : ∀ N, IsMaxNoTripleCard N (f N)) :
    ¬ Tendsto (fun N : ℕ => (f N : ℝ) / N) atTop (𝓝 ((1 : ℝ) / 2)) := by
  sorry

/--
One can take either $A$ to be all odd integers in $[1,N]$ or all integers in $[N/2,N]$ to show
$f(N)\geq (1/2+o(1))N$.
-/
@[category research solved, AMS 11]
theorem erdos_302.variants.lower_half (f : ℕ → ℕ) (hf : ∀ N, IsMaxNoTripleCard N (f N))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ((1 : ℝ) / 2 - ε) * N ≤ f N := by
  sorry

/-- The equation in `ℕ`. -/
lemma e302_nat_eq {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : (1 : ℚ) / a = 1 / b + 1 / c) : b * c = a * b + a * c := by
  have ha' : (a : ℚ) ≠ 0 := by positivity
  have hb' : (b : ℚ) ≠ 0 := by positivity
  have hc' : (c : ℚ) ≠ 0 := by positivity
  field_simp at h
  have h' : ((b * c : ℕ) : ℚ) = ((a * b + a * c : ℕ) : ℚ) := by push_cast; linarith
  exact_mod_cast h'

/-- Two odd entries give a parity contradiction. -/
lemma e302_parity {a b c : ℕ} (h : b * c = a * b + a * c)
    (hodd : (Odd a ∧ Odd b) ∨ (Odd a ∧ Odd c) ∨ (Odd b ∧ Odd c)) : False := by
  have := congrArg Even h
  rcases hodd with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
  · rw [← Nat.not_even_iff_odd] at h1 h2
    simp [Nat.even_add, Nat.even_mul, h1, h2] at this
    try (rw [← Nat.not_even_iff_odd] at this; tauto)

/-- `x` is small (odd, `4x ≤ N`) or big (`N ≤ 2x ≤ 2N`). -/
def e302Set (N : ℕ) : Finset ℕ :=
  (Finset.range (N / 8)).image (fun i => 2 * i + 1) ∪ Finset.Icc ((N + 1) / 2) N

lemma e302_mem {N x : ℕ} (hx : x ∈ e302Set N) : (Odd x ∧ 4 * x ≤ N) ∨ (N ≤ 2 * x ∧ x ≤ N) := by
  simp only [e302Set, Finset.mem_union, Finset.mem_image, Finset.mem_range, Finset.mem_Icc] at hx
  rcases hx with ⟨i, hi, rfl⟩ | ⟨h1, h2⟩
  · left; exact ⟨⟨i, by ring⟩, by omega⟩
  · right; omega

lemma e302_noTriple (N : ℕ) (hN : 1 ≤ N) : NoUnitFractionTriple (e302Set N) := by
  intro a ha b hb c hc hab hac hbc h
  have pos : ∀ x ∈ e302Set N, 0 < x := by
    intro x hx
    rcases e302_mem hx with ⟨ho, -⟩ | ⟨h1, -⟩
    · exact ho.pos
    · omega
  have e := e302_nat_eq (pos a ha) (pos b hb) (pos c hc) h
  have ha0 := pos a ha
  have hb0 := pos b hb
  have hc0 := pos c hc
  rcases e302_mem ha with ⟨oa, sa⟩ | ⟨ba1, ba2⟩ <;>
  rcases e302_mem hb with ⟨ob, sb⟩ | ⟨bb1, bb2⟩ <;>
  rcases e302_mem hc with ⟨oc, sc⟩ | ⟨bc1, bc2⟩
  · exact e302_parity e (Or.inl ⟨oa, ob⟩)
  · exact e302_parity e (Or.inl ⟨oa, ob⟩)
  · exact e302_parity e (Or.inr (Or.inl ⟨oa, oc⟩))
  · -- a small, b c big: 4bc > N(b+c) ≥ 4a(b+c)
    have h1 : N * (b + c) < 4 * (b * c) := by
      rcases Nat.lt_or_gt_of_ne hbc with hlt | hlt <;> nlinarith
    nlinarith
  · exact e302_parity e (Or.inr (Or.inr ⟨ob, oc⟩))
  · -- b small, a c big: a ≥ 2b so ac ≥ 2bc
    nlinarith
  · -- c small, a b big
    nlinarith
  · -- all big: 2bc < N(b+c) ≤ 2a(b+c)
    have h1 : 2 * (b * c) < N * (b + c) := by
      rcases Nat.lt_or_gt_of_ne hbc with hlt | hlt <;> nlinarith
    nlinarith

lemma e302_card (N : ℕ) : 5 * N ≤ 8 * (e302Set N).card + 7 := by
  have hdisj : Disjoint ((Finset.range (N / 8)).image (fun i => 2 * i + 1))
      (Finset.Icc ((N + 1) / 2) N) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc] at hx hx'
    obtain ⟨i, hi, rfl⟩ := hx
    omega
  rw [e302Set, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ (fun i j hij => by omega),
    Finset.card_range, Nat.card_Icc]
  omega

lemma e302_le_f {f : ℕ → ℕ} (hf : ∀ N, IsMaxNoTripleCard N (f N)) (N : ℕ) (hN : 1 ≤ N) :
    5 * N ≤ 8 * f N + 7 := by
  have hmem : (e302Set N).card ∈ {k | ∃ A ⊆ Finset.Icc 1 N, NoUnitFractionTriple A ∧ A.card = k} := by
    refine ⟨e302Set N, ?_, e302_noTriple N hN, rfl⟩
    intro x hx
    rw [Finset.mem_Icc]
    rcases e302_mem hx with ⟨ho, h⟩ | ⟨h1, h2⟩
    · exact ⟨ho.pos, by omega⟩
    · omega
  have := (hf N).2 hmem
  have := e302_card N
  omega

/--
Stijn Cambie has observed that
$$f(N)\geq (5/8+o(1))N,$$
taking $A$ to be all odd integers $\leq N/4$ and all integers in $[N/2,N]$.
-/
@[category research solved, AMS 11]
theorem erdos_302.variants.lower_five_eighths (f : ℕ → ℕ) (hf : ∀ N, IsMaxNoTripleCard N (f N))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ((5 : ℝ) / 8 - ε) * N ≤ f N := by
  filter_upwards [eventually_ge_atTop (⌈1 / ε⌉₊ + 1)] with N hN
  have h := e302_le_f hf N (by omega)
  have hr : (5 : ℝ) * N ≤ 8 * f N + 7 := by exact_mod_cast h
  have hNe : 1 / ε ≤ N := by
    have := Nat.le_ceil (1 / ε)
    have : ((⌈1 / ε⌉₊ : ℕ) : ℝ) ≤ N := by exact_mod_cast (by omega : ⌈1 / ε⌉₊ ≤ N)
    linarith
  have h1 : 1 ≤ ε * N := by
    rw [div_le_iff₀ hε] at hNe; linarith
  nlinarith

/--
Wouter van Doorn has proved [va25] that
$$f(N) \leq (9/10+o(1))N.$$
-/
@[category research solved, AMS 11]
theorem erdos_302.variants.upper_nine_tenths (f : ℕ → ℕ) (hf : ∀ N, IsMaxNoTripleCard N (f N))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (f N : ℝ) ≤ ((9 : ℝ) / 10 + ε) * N := by
  sorry

/--
Kenta Kitamura (KitaKen1 on GitHub) has given a Lean proof
([erdos-302-upper-bound](https://github.com/KitaKen1/erdos-302-upper-bound)) that
$$f(N) \leq (0.8461739827964010+o(1))N.$$
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/erdos-302-upper-bound/blob/9447ceb/lean/Erdos302ReflectiveUpperFC.lean#L92-L99"]
theorem erdos_302.variants.upper_0_8461739827964010 (f : ℕ → ℕ)
    (hf : ∀ N, IsMaxNoTripleCard N (f N)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (f N : ℝ) ≤ ((8461739827964010 : ℝ) / 10000000000000000 + ε) * N := by
  sorry

end Erdos302
