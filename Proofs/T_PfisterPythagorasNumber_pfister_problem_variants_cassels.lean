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
# Pfister's problem on the Pythagoras number of $\mathbb{R}(X_1, \dots, X_n)$

The Pythagoras number $p(K)$ of a field $K$ is the least $p$ such that every sum of squares in
$K$ is a sum of $p$ squares, i.e. the least element of `pythagorasBounds K`.

Artin's solution of Hilbert's 17th problem shows that a positive semidefinite rational function
in $\mathbb{R}(X_1, \dots, X_n)$ is a sum of squares, and Pfister showed that $2^n$ squares
suffice ([Pfister1967, Theorem 1]; for the field, Corollary 1 of Theorem 2 in [Pfister1971]).
Since sums of squares are positive semidefinite, $p(\mathbb{R}(X_1, \dots, X_n)) \le 2^n$
[Pfister1995, p. 95].

Problem 1 of [Pfister1971, §4] asks for the true value of $p(\mathbb{R}(X_1, \dots, X_n))$.
The question is often posed as: is $p(\mathbb{R}(X_1, \dots, X_n)) = 2^n$, i.e. is Pfister's
bound optimal? See e.g. [Benoist2017, Question 0.2].

Problem 1 itself quotes the lower bound $n + 1 \le p(\mathbb{R}(X_1, \dots, X_n))$ from Cassels'
theorem [Cassels1964]. For $n \ge 2$ the best known bounds are
$n + 2 \le p(\mathbb{R}(X_1, \dots, X_n)) \le 2^n$ [Pfister1995, p. 97], where the lower bound
follows from the Cassels–Ellison–Pfister theorem [CEP1971]. The bounds agree for $n = 2$, so the
value is known for $n \le 2$ and open for every $n \ge 3$. The survey
[MerkurjevParimala2025, §5.2] records the question as open even for $\mathbb{R}(X_1, X_2, X_3)$
(Question 5.7).

*References:*
- [Pfister1971] A. Pfister, *Sums of squares in real function fields*, pp. 297–300 in Actes du
  Congrès International des Mathématiciens, Tome 1 (Nice, 1970), Gauthier-Villars, 1971,
  [IMU scan](https://www.mathunion.org/fileadmin/ICM/Proceedings/ICM1970.1/ICM1970.1.ocr.pdf).
- [Pfister1967] A. Pfister, *Zur Darstellung definiter Funktionen als Summe von Quadraten*,
  Invent. Math. 4 (1967), 229–237, [doi:10.1007/BF01425382](https://doi.org/10.1007/BF01425382).
- [Cassels1964] J. W. S. Cassels, *On the representation of rational functions as sums of squares*,
  Acta Arith. 9 (1964), 79–82, [doi:10.4064/aa-9-1-79-82](https://doi.org/10.4064/aa-9-1-79-82).
- [Pfister1995] A. Pfister, *Quadratic forms with applications to algebraic geometry and
  topology*, London Math. Soc. Lecture Note Ser. 217, Cambridge University Press, 1995.
- [CEP1971] J. W. S. Cassels, W. J. Ellison, A. Pfister, *On sums of squares and on elliptic
  curves over function fields*, J. Number Theory 3 (1971), 125–149,
  [doi:10.1016/0022-314X(71)90030-8](https://doi.org/10.1016/0022-314X(71)90030-8).
- [Benoist2017] O. Benoist, *On Hilbert's 17th problem in low degree*, Algebra Number Theory 11
  (2017), 929–959, [doi:10.2140/ant.2017.11.929](https://doi.org/10.2140/ant.2017.11.929),
  [arXiv:1602.07330](https://arxiv.org/abs/1602.07330).
- [MerkurjevParimala2025] A. Merkurjev, R. Parimala, *Quadratic forms beyond arithmetic*, Notices
  Amer. Math. Soc. 72 (2025), no. 7, 711–718,
  [doi:10.1090/noti3192](https://doi.org/10.1090/noti3192).
-/

@[expose] public section

namespace PfisterPythagorasNumber

/-- Every sum of squares in $\mathbb{R}$ is a square and $1$ is not a sum of zero squares, so
$p(\mathbb{R}) = 1$. -/
@[category test, AMS 11]
theorem isLeast_pythagorasBounds_real : IsLeast (pythagorasBounds ℝ) 1 := by
  refine ⟨fun a ha ↦ ⟨fun _ ↦ √a, ?_⟩, fun p hp ↦ ?_⟩
  · simp [Real.mul_self_sqrt ha.nonneg]
  · rcases Nat.eq_zero_or_pos p with rfl | h
    · obtain ⟨f, hf⟩ := hp 1 IsSumSq.one
      simp at hf
    · exact h

/--
**Pfister's problem** (Problem 1 of [Pfister1971, §4]): what is the true value of
$p(\mathbb{R}(X_1, \dots, X_n))$, as a function of $n$? It is $1$, $2$, $4$ for $n = 0, 1, 2$
(`pfister_problem.variants.zero`, `pfister_problem.variants.one`, `pfister_problem.variants.two`)
and open for every $n \ge 3$, where only the bounds
$n + 2 \le p(\mathbb{R}(X_1, \dots, X_n)) \le 2^n$ are known.
-/
@[category research open, AMS 11 12 14]
theorem pfister_problem :
    let p : ℕ → ℕ := answer(sorry)
    ∀ n, IsLeast (pythagorasBounds (MvRatFunc (Fin n) ℝ)) (p n) := by
  sorry

/--
Pfister's problem in its common yes/no form (e.g. Question 0.2 of [Benoist2017]): is
$p(\mathbb{R}(X_1, \dots, X_n)) = 2^n$ for every $n$, i.e. is Pfister's bound optimal? This
holds for $n \le 2$ and is open for every $n \ge 3$.
-/
@[category research open, AMS 11 12 14]
theorem pfister_problem.variants.eq_two_pow :
    answer(sorry) ↔ ∀ n : ℕ, IsLeast (pythagorasBounds (MvRatFunc (Fin n) ℝ)) (2 ^ n) := by
  sorry

/--
**Pfister's theorem**: every sum of squares in $\mathbb{R}(X_1, \dots, X_n)$ is a sum of $2^n$
squares [Pfister1995, p. 95]; this is Corollary 1 of Theorem 2 in [Pfister1971]. For positive
semidefinite polynomials it is [Pfister1967, Theorem 1], the quantitative refinement of Artin's
theorem `Hilbert17.hilbert_17th_problem` in `FormalConjectures/HilbertProblems/17.lean`.
-/
@[category research solved, AMS 11 12 14]
theorem pfister_problem.variants.upper_bound (n : ℕ) :
    2 ^ n ∈ pythagorasBounds (MvRatFunc (Fin n) ℝ) := by
  sorry

open Polynomial in
/-- Anisotropy of the sum of `n` squares lifts from `K` to `K[X]`. -/
lemma pf_aniso_poly {K : Type*} [Field K] {n : ℕ}
    (hK : ∀ c : Fin n → K, ∑ j, c j ^ 2 = 0 → c = 0) (c : Fin n → K[X])
    (hc : ∑ j, c j ^ 2 = 0) : c = 0 := by
  classical
  by_contra hne
  -- the maximal degree among the `c j`
  obtain ⟨j0, hj0⟩ := Function.ne_iff.mp hne
  set D := Finset.univ.sup (fun j => (c j).natDegree) with hD
  have hle : ∀ j, (c j).natDegree ≤ D := fun j => Finset.le_sup (f := fun j => (c j).natDegree)
    (Finset.mem_univ j)
  have hcoeff : ∀ j, (c j ^ 2).coeff (2 * D) = (c j).coeff D ^ 2 := by
    intro j
    rw [sq, sq, two_mul]
    exact coeff_mul_add_eq_of_natDegree_le (hle j) (hle j)
  have h0 : ∑ j, (c j).coeff D ^ 2 = 0 := by
    have := congrArg (fun p => p.coeff (2 * D)) hc
    simp only [finsetSum_coeff, coeff_zero] at this
    rw [← this]
    exact Finset.sum_congr rfl (fun j _ => (hcoeff j).symm)
  have hz := hK (fun j => (c j).coeff D) h0
  -- some `c j` has degree exactly `D` and is nonzero
  obtain ⟨j1, -, hj1⟩ := Finset.exists_mem_eq_sup Finset.univ ⟨j0, Finset.mem_univ _⟩
    (fun j => (c j).natDegree)
  have hlead : (c j1).coeff D = 0 := congrFun hz j1
  rw [hD, hj1, coeff_natDegree, leadingCoeff_eq_zero] at hlead
  -- then all `c j` have degree `0`, and constant coefficient `0`
  have hD0 : D = 0 := by rw [hD, hj1, hlead, natDegree_zero]
  have : c j0 = 0 := by
    have h1 : (c j0).natDegree = 0 := Nat.le_zero.mp (hD0 ▸ hle j0)
    have h2 : (c j0).coeff 0 = 0 := by rw [← hD0]; exact congrFun hz j0
    rw [eq_C_of_natDegree_eq_zero h1, h2, C_0]
  exact hj0 this

open Polynomial in
/-- The reflection step: algebraic identities. -/
lemma pf_reflect {R : Type*} [CommRing R] {n : ℕ} (f q P T : R) (a b : Fin n → R)
    (h : q ^ 2 * f = ∑ j, a j ^ 2) (hP : P = f - ∑ j, b j ^ 2)
    (hT : T = 2 * (f * q - ∑ j, a j * b j)) :
    (P * q - T) ^ 2 * f = ∑ j, (P * a j - T * b j) ^ 2 ∧
      q * (P * q - T) = -∑ j, (a j - q * b j) ^ 2 := by
  have e1 : ∑ j, (P * a j - T * b j) ^ 2 =
      P ^ 2 * ∑ j, a j ^ 2 - 2 * P * T * ∑ j, a j * b j + T ^ 2 * ∑ j, b j ^ 2 := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have e2 : ∑ j, (a j - q * b j) ^ 2 =
      ∑ j, a j ^ 2 - 2 * q * ∑ j, a j * b j + q ^ 2 * ∑ j, b j ^ 2 := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  constructor
  · rw [e1, ← h, hP, hT]; ring
  · rw [e2, ← h, hP, hT]; ring

open Polynomial in
/-- W1 (Cassels' lemma): if `q² f` is a sum of `n` squares in `K[X]` with `q ≠ 0`, and the sum of
`n` squares is anisotropic over `K`, then `f` is a sum of `n` squares in `K[X]`. -/
theorem pf_cassels_lemma {K : Type*} [Field K] {n : ℕ}
    (hK : ∀ c : Fin n → K, ∑ j, c j ^ 2 = 0 → c = 0) (f : K[X]) :
    ∀ (d : ℕ) (q : K[X]) (a : Fin n → K[X]), q.natDegree = d → q ≠ 0 →
      q ^ 2 * f = ∑ j, a j ^ 2 → ∃ p : Fin n → K[X], f = ∑ j, p j ^ 2 := by
  classical
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro q a hd hq h
    obtain ⟨b, hb⟩ : ∃ b : Fin n → K[X], b = fun j => a j / q := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c : Fin n → K[X], c = fun j => a j % q := ⟨_, rfl⟩
    have hac : ∀ j, a j - q * b j = c j := by
      intro j
      have := EuclideanDomain.div_add_mod (a j) q
      rw [hb, hc]; linear_combination -this
    obtain ⟨P, hPdef⟩ : ∃ P : K[X], P = f - ∑ j, b j ^ 2 := ⟨_, rfl⟩
    obtain ⟨T, hTdef⟩ : ∃ T : K[X], T = 2 * (f * q - ∑ j, a j * b j) := ⟨_, rfl⟩
    obtain ⟨h1, h2⟩ := pf_reflect f q P T a b h hPdef hTdef
    by_cases hP : P = 0
    · exact ⟨b, sub_eq_zero.mp (hPdef ▸ hP)⟩
    by_cases hc0 : c = 0
    · -- then `a = q b` and `P = 0`
      exfalso
      apply hP
      have hab : ∀ j, a j = q * b j := fun j => by
        have := hac j; rw [hc0] at this; exact sub_eq_zero.mp this
      have hsq : ∑ j, a j ^ 2 = q ^ 2 * ∑ j, b j ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by rw [hab j]; ring)
      have : q ^ 2 * P = 0 := by
        rw [hPdef, mul_sub, h, hsq, sub_self]
      exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero 2 hq)
    -- the new denominator
    obtain ⟨q', hq'def⟩ : ∃ q' : K[X], q' = P * q - T := ⟨_, rfl⟩
    rw [← hq'def] at h1 h2
    have hsum : ∑ j, c j ^ 2 ≠ 0 := fun h0 => hc0 (pf_aniso_poly hK c h0)
    have hqq' : q * q' = -∑ j, c j ^ 2 := by
      rw [h2]
      exact congrArg Neg.neg (Finset.sum_congr rfl (fun j _ => by rw [hac j]))
    have hq' : q' ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hqq'
      exact hsum (neg_eq_zero.mp hqq'.symm)
    have hcj : ∀ j, c j = a j % q := fun j => congrFun hc j
    have hdpos : 0 < q.natDegree := by
      by_contra hd0
      push Not at hd0
      have hunit : IsUnit q := by
        rw [Polynomial.isUnit_iff]
        exact ⟨q.coeff 0, isUnit_iff_ne_zero.mpr (by
          intro h0; apply hq
          rw [eq_C_of_natDegree_eq_zero (Nat.le_zero.mp hd0), h0, C_0]),
          (eq_C_of_natDegree_eq_zero (Nat.le_zero.mp hd0)).symm⟩
      apply hc0; funext j
      rw [hcj j]
      exact (EuclideanDomain.mod_eq_zero.mpr (hunit.dvd))
    have hcdeg : ∀ j, (c j).natDegree < q.natDegree ∨ c j = 0 := by
      intro j
      by_cases hcj0 : c j = 0
      · exact Or.inr hcj0
      · left
        refine natDegree_lt_natDegree hcj0 ?_
        rw [hcj j]; exact EuclideanDomain.mod_lt (a j) hq
    have hsumdeg : (∑ j, c j ^ 2).natDegree < 2 * q.natDegree := by
      have hle : (∑ j, c j ^ 2).natDegree ≤ 2 * (q.natDegree - 1) := by
        apply natDegree_sum_le_of_forall_le
        intro j _
        rcases hcdeg j with hj | hj
        · calc (c j ^ 2).natDegree ≤ 2 * (c j).natDegree := natDegree_pow_le
            _ ≤ 2 * (q.natDegree - 1) := by omega
        · rw [hj]; simp
      omega
    have hdeg' : q'.natDegree < d := by
      have := congrArg natDegree hqq'
      rw [natDegree_mul hq hq', natDegree_neg] at this
      omega
    exact ih q'.natDegree hdeg' q' (fun j => P * a j - T * b j) rfl hq' h1

open Polynomial in
/-- Householder step: from unit vector `α` and `β ⟂ α`, a vector of one coordinate less with
the same norm as `β`. -/
lemma pf_householder {K : Type*} [Field K] {n : ℕ}
    (hK : ∀ c : Fin (n + 1) → K, ∑ j, c j ^ 2 = 0 → c = 0) (α β : Fin (n + 1) → K) (d : K)
    (h1 : ∑ j, α j ^ 2 = 1) (h2 : ∑ j, α j * β j = 0) (h3 : ∑ j, β j ^ 2 = d) :
    ∃ g : Fin n → K, d = ∑ i, g i ^ 2 := by
  rw [Fin.sum_univ_succ] at h1 h2 h3
  by_cases hα : α 0 = 1
  · have hz : ∑ i : Fin n, α i.succ ^ 2 = 0 := by rw [hα] at h1; linear_combination h1
    have hz' := hK (Fin.cons 0 (fun i => α i.succ)) (by
      rw [Fin.sum_univ_succ]; simpa using hz)
    have hα0 : ∀ i : Fin n, α i.succ = 0 := fun i => by
      have := congrFun hz' i.succ; simpa using this
    have hβ0 : β 0 = 0 := by
      simp only [hα0, zero_mul, Finset.sum_const_zero, add_zero, hα, one_mul] at h2
      exact h2
    refine ⟨fun i => β i.succ, ?_⟩
    rw [← h3, hβ0]; ring
  · have hne : 1 - α 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hα)
    refine ⟨fun i => β i.succ + β 0 / (1 - α 0) * α i.succ, ?_⟩
    have e : ∑ i : Fin n, (β i.succ + β 0 / (1 - α 0) * α i.succ) ^ 2 =
        ∑ i : Fin n, β i.succ ^ 2 + 2 * (β 0 / (1 - α 0)) * ∑ i : Fin n, α i.succ * β i.succ +
          (β 0 / (1 - α 0)) ^ 2 * ∑ i : Fin n, α i.succ ^ 2 := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have s1 : ∑ i : Fin n, α i.succ ^ 2 = 1 - α 0 ^ 2 := by linear_combination h1
    have s2 : ∑ i : Fin n, α i.succ * β i.succ = -(α 0 * β 0) := by linear_combination h2
    have s3 : ∑ i : Fin n, β i.succ ^ 2 = d - β 0 ^ 2 := by linear_combination h3
    rw [e, s1, s2, s3]
    field_simp
    ring

open Polynomial in
/-- W2: if `X² + d` is a sum of `n + 1` squares in `K[X]`, then `d` is a sum of `n` squares
in `K` (assuming the sum of `n + 1` squares is anisotropic and `2 ≠ 0`). -/
theorem pf_X_sq_add {K : Type*} [Field K] {n : ℕ} (h2 : (2 : K) ≠ 0)
    (hK : ∀ c : Fin (n + 1) → K, ∑ j, c j ^ 2 = 0 → c = 0) (d : K) (p : Fin (n + 1) → K[X])
    (hp : X ^ 2 + C d = ∑ j, p j ^ 2) : ∃ g : Fin n → K, d = ∑ i, g i ^ 2 := by
  classical
  obtain ⟨D, hD⟩ : ∃ D, D = Finset.univ.sup (fun j => (p j).natDegree) := ⟨_, rfl⟩
  have hle : ∀ j, (p j).natDegree ≤ D := fun j => hD ▸
    Finset.le_sup (f := fun j => (p j).natDegree) (Finset.mem_univ j)
  have hD1 : D ≤ 1 := by
    by_contra hD2
    push Not at hD2
    have hcoeff : ∀ j, (p j ^ 2).coeff (2 * D) = (p j).coeff D ^ 2 := by
      intro j
      rw [sq, sq, two_mul]
      exact coeff_mul_add_eq_of_natDegree_le (hle j) (hle j)
    have h0 : ∑ j, (p j).coeff D ^ 2 = 0 := by
      have := congrArg (fun p => p.coeff (2 * D)) hp
      simp only [finsetSum_coeff, coeff_add, coeff_X_pow, coeff_C] at this
      rw [if_neg (by omega), if_neg (by omega), add_zero] at this
      rw [this]
      exact Finset.sum_congr rfl (fun j _ => (hcoeff j).symm)
    have hz := hK (fun j => (p j).coeff D) h0
    obtain ⟨j1, -, hj1⟩ := Finset.exists_mem_eq_sup Finset.univ ⟨0, Finset.mem_univ _⟩
      (fun j => (p j).natDegree)
    have hlead : (p j1).coeff D = 0 := congrFun hz j1
    rw [hD, hj1, coeff_natDegree, leadingCoeff_eq_zero] at hlead
    have : D = 0 := by rw [hD, hj1, hlead, natDegree_zero]
    omega
  have hform : ∀ j, p j = C ((p j).coeff 1) * X + C ((p j).coeff 0) := fun j =>
    eq_X_add_C_of_natDegree_le_one ((hle j).trans hD1)
  obtain ⟨α, hα⟩ : ∃ α : Fin (n + 1) → K, α = fun j => (p j).coeff 1 := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : Fin (n + 1) → K, β = fun j => (p j).coeff 0 := ⟨_, rfl⟩
  have hexp : ∑ j, p j ^ 2 = C (∑ j, α j ^ 2) * X ^ 2 + C (2 * ∑ j, α j * β j) * X +
      C (∑ j, β j ^ 2) := by
    simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hform j, hα, hβ]
    simp only [map_pow, map_ofNat]
    ring
  rw [hexp] at hp
  have c2 := congrArg (fun q => q.coeff 2) hp
  have c1 := congrArg (fun q => q.coeff 1) hp
  have c0 := congrArg (fun q => q.coeff 0) hp
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C] at c2 c1 c0
  norm_num at c2 c1 c0
  exact pf_householder hK α β d c2.symm (c1.resolve_left h2) c0.symm

open Polynomial in
/-- Clearing denominators in a representation as a sum of squares over a fraction field. -/
lemma pf_clear {A : Type*} [CommRing A] [IsDomain A] {m : ℕ} (u : A)
    (g : Fin m → FractionRing A) (h : algebraMap A (FractionRing A) u = ∑ j, g j ^ 2) :
    ∃ Q : A, Q ≠ 0 ∧ ∃ a : Fin m → A, Q ^ 2 * u = ∑ j, a j ^ 2 ∧
      ∀ j, algebraMap A (FractionRing A) (a j) = algebraMap A (FractionRing A) Q * g j := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors A) Finset.univ g
  have hb' : ∀ j, ∃ a : A, algebraMap A (FractionRing A) a =
      algebraMap A (FractionRing A) (b : A) * g j := fun j => by
    obtain ⟨a, ha⟩ := hb j (Finset.mem_univ j)
    exact ⟨a, by rw [ha, Algebra.smul_def]⟩
  choose a ha using hb'
  refine ⟨b, nonZeroDivisors.coe_ne_zero b, a, ?_, ha⟩
  apply IsFractionRing.injective A (FractionRing A)
  rw [map_mul, map_pow, h, map_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by rw [map_pow, ha j]; ring)

open Polynomial in
/-- Sums of squares of real polynomials are anisotropic. -/
lemma pf_aniso_mvPoly {σ : Type*} {m : ℕ} (a : Fin m → MvPolynomial σ ℝ)
    (h : ∑ j, a j ^ 2 = 0) : a = 0 := by
  funext j
  apply MvPolynomial.funext
  intro x
  have := congrArg (MvPolynomial.eval x) h
  simp only [map_sum, map_pow, map_zero] at this
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).mp this j
    (Finset.mem_univ j)
  simpa using h0

open Polynomial in
/-- Sums of squares of real rational functions are anisotropic. -/
lemma pf_aniso_ratFunc {σ : Type*} {m : ℕ} (g : Fin m → FractionRing (MvPolynomial σ ℝ))
    (h : ∑ j, g j ^ 2 = 0) : g = 0 := by
  obtain ⟨Q, hQ, a, ha, hag⟩ := pf_clear (0 : MvPolynomial σ ℝ) g (by rw [map_zero, h])
  rw [mul_zero] at ha
  have ha0 := pf_aniso_mvPoly a ha.symm
  funext j
  have := hag j
  rw [ha0, Pi.zero_apply, map_zero] at this
  have hQ' : algebraMap (MvPolynomial σ ℝ) (FractionRing (MvPolynomial σ ℝ)) Q ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
  exact (mul_eq_zero.mp this.symm).resolve_left hQ'

open Polynomial in
/-- W3: the induction step of Cassels' theorem. -/
lemma pf_cassels_step (n : ℕ)
    (g : Fin (n + 1) → FractionRing (MvPolynomial (Fin (n + 1)) ℝ))
    (h : algebraMap (MvPolynomial (Fin (n + 1)) ℝ) (FractionRing (MvPolynomial (Fin (n + 1)) ℝ))
      (1 + ∑ i, MvPolynomial.X i * MvPolynomial.X i) = ∑ j, g j ^ 2) :
    ∃ g' : Fin n → FractionRing (MvPolynomial (Fin n) ℝ),
      algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ))
        (1 + ∑ i, MvPolynomial.X i * MvPolynomial.X i) = ∑ j, g' j ^ 2 := by
  obtain ⟨Q, hQ, a, ha, -⟩ := pf_clear _ g h
  obtain ⟨ψ, hψ⟩ : ∃ ψ : MvPolynomial (Fin (n + 1)) ℝ →+*
      (FractionRing (MvPolynomial (Fin n) ℝ))[X], ψ =
      (Polynomial.mapRingHom (algebraMap (MvPolynomial (Fin n) ℝ)
        (FractionRing (MvPolynomial (Fin n) ℝ)))).comp
        (MvPolynomial.finSuccEquiv ℝ n : MvPolynomial (Fin (n + 1)) ℝ →+* _) := ⟨_, rfl⟩
  have hinj : Function.Injective ψ := by
    rw [hψ]
    exact (Polynomial.map_injective _ (IsFractionRing.injective _ _)).comp
      (MvPolynomial.finSuccEquiv ℝ n).injective
  have hX0 : ψ (MvPolynomial.X 0) = X := by
    rw [hψ]; simp [MvPolynomial.finSuccEquiv_X_zero]
  have hXs : ∀ i : Fin n, ψ (MvPolynomial.X i.succ) = C (algebraMap (MvPolynomial (Fin n) ℝ)
        (FractionRing (MvPolynomial (Fin n) ℝ)) (MvPolynomial.X i)) := by
    intro i; rw [hψ]; simp [MvPolynomial.finSuccEquiv_X_succ]
  have hf : ψ (1 + ∑ i, MvPolynomial.X i * MvPolynomial.X i) =
      X ^ 2 + C (algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ))
        (1 + ∑ i, MvPolynomial.X i * MvPolynomial.X i)) := by
    rw [Fin.sum_univ_succ]
    simp only [map_add, map_one, map_mul, map_sum, hX0, hXs]
    ring
  have hK : ∀ c : Fin (n + 1) → FractionRing (MvPolynomial (Fin n) ℝ),
      ∑ j, c j ^ 2 = 0 → c = 0 := fun c hc => pf_aniso_ratFunc c hc
  have h' := congrArg ψ ha
  rw [map_mul, map_pow, map_sum, hf] at h'
  simp only [map_pow] at h'
  obtain ⟨p, hp⟩ := pf_cassels_lemma hK _ _ (ψ Q) (fun j => ψ (a j)) rfl
    (by rwa [Ne, map_eq_zero_iff _ hinj]) h'
  have h2 : (2 : FractionRing (MvPolynomial (Fin n) ℝ)) ≠ 0 := two_ne_zero
  exact pf_X_sq_add h2 hK _ p hp

open Polynomial in
/-- W4: Cassels' theorem, `^ 2` form. -/
theorem pf_cassels_aux (n : ℕ) (g : Fin n → FractionRing (MvPolynomial (Fin n) ℝ)) :
    algebraMap (MvPolynomial (Fin n) ℝ) (FractionRing (MvPolynomial (Fin n) ℝ))
      (1 + ∑ i, MvPolynomial.X i * MvPolynomial.X i) ≠ ∑ j, g j ^ 2 := by
  induction n with
  | zero =>
    intro h
    simp at h
  | succ n ih =>
    intro h
    obtain ⟨g', hg'⟩ := pf_cassels_step n g h
    exact ih g' hg'

/--
**Cassels' theorem** [Cassels1964], as quoted in Problem 1 of [Pfister1971, §4]:
$1 + X_1^2 + \dots + X_n^2$ is not a sum of $n$ squares in $\mathbb{R}(X_1, \dots, X_n)$.
-/
@[category research solved, AMS 11 12 14]
theorem pfister_problem.variants.cassels (n : ℕ) :
    ¬IsSumSqOfLength n (algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ)
      (1 + ∑ i, MvPolynomial.X i * MvPolynomial.X i)) := by
  rintro ⟨f, hf⟩
  exact pf_cassels_aux n f (by rw [hf]; exact Finset.sum_congr rfl (fun j _ => (sq _).symm))

/--
The lower bound $n + 1 \le p(\mathbb{R}(X_1, \dots, X_n))$ quoted in Problem 1 of
[Pfister1971, §4]: $1 + X_1^2 + \dots + X_n^2$ is a sum of $n + 1$ squares but, by Cassels'
theorem `pfister_problem.variants.cassels`, not of $n$ squares. It is superseded by
`pfister_problem.variants.lower_bound` for $n \ge 2$.
-/
@[category research solved, AMS 11 12 14]
theorem pfister_problem.variants.add_one_le (n : ℕ) {p : ℕ}
    (hp : p ∈ pythagorasBounds (MvRatFunc (Fin n) ℝ)) : n + 1 ≤ p := by
  by_contra h
  have hsq : IsSumSqOfLength (n + 1) (algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ)
      (1 + ∑ i, MvPolynomial.X i * MvPolynomial.X i)) :=
    ⟨Fin.cons 1 fun i ↦ algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ)
      (MvPolynomial.X i), by simp [Fin.sum_univ_succ, map_sum]⟩
  exact pfister_problem.variants.cassels n ((hp _ hsq.isSumSq).of_le (by omega))

/--
The lower bound $n + 2 \le p(\mathbb{R}(X_1, \dots, X_n))$ for $n \ge 2$ [Pfister1995, p. 97],
a consequence of the Cassels–Ellison–Pfister theorem [CEP1971]. The hypothesis $n \ge 2$ is
needed: $p(\mathbb{R}(X)) = 2 < 3$.
-/
@[category research solved, AMS 11 12 14]
theorem pfister_problem.variants.lower_bound (n : ℕ) (hn : 2 ≤ n) {p : ℕ}
    (hp : p ∈ pythagorasBounds (MvRatFunc (Fin n) ℝ)) : n + 2 ≤ p := by
  sorry

/--
$p(\mathbb{R}(X_1, \dots, X_n)) = 1$ for $n = 0$, i.e. $p(\mathbb{R}) = 1$: here the bounds $n + 1$
and $2^n$ of `pfister_problem.variants.add_one_le` and `pfister_problem.variants.upper_bound`
agree. Compare `isLeast_pythagorasBounds_real`, the same value for `ℝ` itself.
-/
@[category textbook, AMS 11 12 14]
theorem pfister_problem.variants.zero : IsLeast (pythagorasBounds (MvRatFunc (Fin 0) ℝ)) 1 :=
  ⟨pfister_problem.variants.upper_bound 0,
    fun _ hp ↦ pfister_problem.variants.add_one_le 0 hp⟩

/--
$p(\mathbb{R}(X)) = 2$ [Pfister1995, p. 96]: Pfister's bound gives $p \le 2$, and Cassels'
theorem `pfister_problem.variants.cassels` gives $p \ge 2$ through
`pfister_problem.variants.add_one_le`, since $1 + X^2$ is a sum of two squares that is not a
square in $\mathbb{R}(X)$.
-/
@[category textbook, AMS 11 12 14]
theorem pfister_problem.variants.one : IsLeast (pythagorasBounds (MvRatFunc (Fin 1) ℝ)) 2 :=
  ⟨pfister_problem.variants.upper_bound 1,
    fun _ hp ↦ pfister_problem.variants.add_one_le 1 hp⟩

/--
$p(\mathbb{R}(X_1, X_2)) = 4$ [CEP1971], as recorded in [Pfister1971, §4] and [Pfister1995, p. 96]:
the bounds $n + 2$ and $2^n$ agree when $n = 2$.
-/
@[category research solved, AMS 11 12 14]
theorem pfister_problem.variants.two : IsLeast (pythagorasBounds (MvRatFunc (Fin 2) ℝ)) 4 :=
  ⟨pfister_problem.variants.upper_bound 2,
    fun _ hp ↦ pfister_problem.variants.lower_bound 2 le_rfl hp⟩

end PfisterPythagorasNumber
