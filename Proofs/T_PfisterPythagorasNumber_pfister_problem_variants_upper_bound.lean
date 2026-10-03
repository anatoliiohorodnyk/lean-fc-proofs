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

/-- The substitution killing the first `j` variables. -/
noncomputable def pfKill (k : Type*) [Field k] (N j : ℕ) :
    MvPolynomial (Fin N) k →ₐ[k] MvPolynomial (Fin N) k :=
  MvPolynomial.aeval (fun i : Fin N => if (i : ℕ) < j then 0 else MvPolynomial.X i)

lemma pfKill_X (k : Type*) [Field k] (N j : ℕ) (i : Fin N) :
    pfKill k N j (MvPolynomial.X i) = if (i : ℕ) < j then 0 else MvPolynomial.X i := by
  simp [pfKill]

lemma pfKill_comp (k : Type*) [Field k] (N j : ℕ) :
    (pfKill k N (j + 1)).comp (pfKill k N j) = pfKill k N (j + 1) := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [AlgHom.comp_apply, pfKill_X]
  by_cases h : (i : ℕ) < j
  · rw [if_pos h, map_zero, pfKill_X, if_pos (by omega)]
  · rw [if_neg h]

lemma pfKill_height (k : Type*) [Field k] (N j : ℕ) (hj : j ≤ N) :
    (j : ℕ∞) ≤ (RingHom.ker (pfKill k N j).toRingHom).height := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hlt : RingHom.ker (pfKill k N j).toRingHom < RingHom.ker (pfKill k N (j + 1)).toRingHom := by
      refine lt_of_le_of_ne ?_ ?_
      · intro p hp
        rw [RingHom.mem_ker] at hp ⊢
        have := congrArg (fun φ : MvPolynomial (Fin N) k →ₐ[k] MvPolynomial (Fin N) k => φ p)
          (pfKill_comp k N j)
        simp only [AlgHom.comp_apply] at this
        change pfKill k N (j + 1) p = 0
        rw [← this]
        change pfKill k N j p = 0 at hp
        rw [hp, map_zero]
      · intro heq
        have h1 : (MvPolynomial.X ⟨j, by omega⟩ : MvPolynomial (Fin N) k) ∈
            RingHom.ker (pfKill k N (j + 1)).toRingHom := by
          rw [RingHom.mem_ker]
          change pfKill k N (j + 1) _ = 0
          rw [pfKill_X, if_pos (by simp)]
        rw [← heq, RingHom.mem_ker] at h1
        change pfKill k N j _ = 0 at h1
        rw [pfKill_X, if_neg (by simp)] at h1
        exact MvPolynomial.X_ne_zero _ h1
    have := RingHom.ker_isPrime (pfKill k N j).toRingHom
    have := RingHom.ker_isPrime (pfKill k N (j + 1)).toRingHom
    have := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    calc ((j + 1 : ℕ) : ℕ∞) = (j : ℕ∞) + 1 := by push_cast; rfl
      _ ≤ _ := (add_le_add_left (ih (by omega)) 1).trans this

/-- P1: `r` polynomials without constant term in `N > r` variables over an algebraically closed
field have a common nontrivial zero. -/
theorem pf_common_zero {k : Type*} [Field k] [IsAlgClosed k] {N r : ℕ} (hr : r < N)
    (f : Fin r → MvPolynomial (Fin N) k) (hf : ∀ i, MvPolynomial.eval 0 (f i) = 0) :
    ∃ x : Fin N → k, x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (f i) = 0 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨s, hs⟩ : ∃ s : Finset (MvPolynomial (Fin N) k), s = Finset.univ.image f := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : Ideal (MvPolynomial (Fin N) k),
      m = MvPolynomial.vanishingIdeal k {(0 : Fin N → k)} := ⟨_, rfl⟩
  have hae : ∀ (x : Fin N → k) (p : MvPolynomial (Fin N) k),
      MvPolynomial.aeval x p = MvPolynomial.eval x p := fun x p =>
    RingHom.congr_fun (MvPolynomial.coe_aeval_eq_eval x) p
  have hmem : ∀ p, p ∈ m ↔ MvPolynomial.eval 0 p = 0 := by
    intro p
    rw [hm, MvPolynomial.mem_vanishingIdeal_singleton_iff]
    rfl
  have hmprime : m.IsPrime := by
    have : m = RingHom.ker (MvPolynomial.eval (0 : Fin N → k)) := by
      ext p; rw [hmem, RingHom.mem_ker]
    rw [this]; exact RingHom.ker_isPrime _
  have hIm : Ideal.span (s : Set (MvPolynomial (Fin N) k)) ≤ m := by
    rw [Ideal.span_le]
    intro p hp
    rw [hs] at hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
    exact (hmem _).mpr (hf i)
  have hzero : MvPolynomial.zeroLocus k (Ideal.span (s : Set (MvPolynomial (Fin N) k))) =
      {(0 : Fin N → k)} := by
    ext x
    rw [MvPolynomial.mem_zeroLocus_iff, Set.mem_singleton_iff]
    constructor
    · intro hx
      by_contra hx0
      obtain ⟨i, hi⟩ := hcon x hx0
      apply hi
      have := hx (f i) (Ideal.subset_span (by rw [hs]; simp))
      rwa [hae] at this
    · rintro rfl p hp
      rw [hae]
      exact (hmem p).mp (hIm hp)
  have hrad : (Ideal.span (s : Set (MvPolynomial (Fin N) k))).radical = m := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := k), hzero, hm]
  have hmin : m ∈ (Ideal.span (s : Set (MvPolynomial (Fin N) k))).minimalPrimes := by
    refine ⟨⟨hmprime, hIm⟩, ?_⟩
    rintro q ⟨hq, hIq⟩ -
    rw [← hrad]
    exact (Ideal.IsPrime.radical_le_iff hq).mpr hIq
  have h1 : m.height ≤ (s.card : ℕ∞) := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmin
  have h2 : (s.card : ℕ∞) ≤ r := by
    rw [hs]
    exact_mod_cast (Finset.card_image_le.trans (by simp))
  have h3 : RingHom.ker (pfKill k N N).toRingHom ≤ m := by
    intro p hp
    rw [RingHom.mem_ker] at hp
    change pfKill k N N p = 0 at hp
    rw [hmem]
    have hcomp : (MvPolynomial.aeval (0 : Fin N → k)).comp (pfKill k N N) =
        MvPolynomial.aeval (0 : Fin N → k) := by
      apply MvPolynomial.algHom_ext
      intro i
      rw [AlgHom.comp_apply, pfKill_X, if_pos i.2]
      simp
    have := congrArg (fun φ : MvPolynomial (Fin N) k →ₐ[k] k => φ p) hcomp
    simp only [AlgHom.comp_apply, hp, map_zero] at this
    rw [← hae]
    exact this.symm
  have h4 := (pfKill_height k N N le_rfl).trans (Ideal.height_mono h3)
  have : (N : ℕ∞) ≤ r := h4.trans (h1.trans h2)
  have : N ≤ r := by exact_mod_cast this
  omega

/-- Sum of squares of a vector. -/
def pfSq {K : Type*} [Field K] {m : ℕ} (x : Fin m → K) : K := ∑ i, x i ^ 2

/-- Diagonal quadratic form with weights `e`. -/
def pfQ {K : Type*} [Field K] {m : ℕ} (e x : Fin m → K) : K := ∑ i, e i * x i ^ 2

/-- Diagonal bilinear form with weights `e`. -/
def pfB {K : Type*} [Field K] {m : ℕ} (e x y : Fin m → K) : K := ∑ i, e i * x i * y i

lemma pfSq_append {K : Type*} [Field K] {a b : ℕ} (x : Fin a → K) (y : Fin b → K) :
    pfSq (Fin.append x y) = pfSq x + pfSq y := by
  simp [pfSq, Fin.sum_univ_add]

lemma pfQ_append {K : Type*} [Field K] {a b : ℕ} (e x : Fin a → K) (d y : Fin b → K) :
    pfQ (Fin.append e d) (Fin.append x y) = pfQ e x + pfQ d y := by
  simp [pfQ, Fin.sum_univ_add]

lemma pfQ_mul_weights {K : Type*} [Field K] {m : ℕ} (a : K) (e x : Fin m → K) :
    pfQ (fun i => a * e i) x = a * pfQ e x := by
  simp only [pfQ, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

lemma pfQ_one {K : Type*} [Field K] {m : ℕ} (x : Fin m → K) :
    pfQ (fun _ => 1) x = pfSq x := by
  simp [pfQ, pfSq]

lemma pfSq_smul {K : Type*} [Field K] {m : ℕ} (a : K) (x : Fin m → K) :
    pfSq (a • x) = a ^ 2 * pfSq x := by
  simp only [pfSq, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl (fun i _ => by ring)

lemma pfQ_smul {K : Type*} [Field K] {m : ℕ} (a : K) (e x : Fin m → K) :
    pfQ e (a • x) = a ^ 2 * pfQ e x := by
  simp only [pfQ, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl (fun i _ => by ring)

lemma pfQ_add_smul {K : Type*} [Field K] {m : ℕ} (a : K) (e x y : Fin m → K) :
    pfQ e (x + a • y) = pfQ e x + 2 * a * pfB e x y + a ^ 2 * pfQ e y := by
  simp only [pfQ, pfB, Finset.mul_sum, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- The binary identity `⟨u, v⟩ ≅ ⟨u + v, u v (u + v)⟩` on vectors. -/
lemma pfQ_binary {K : Type*} [Field K] {m : ℕ} (u v : K) (e P Q : Fin m → K) :
    u * pfQ e (P - v • Q) + v * pfQ e (P + u • Q) =
      (u + v) * pfQ e P + u * v * (u + v) * pfQ e Q := by
  simp only [pfQ, Finset.mul_sum, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

lemma pf_append_eq_zero {K : Type*} [Field K] {a b : ℕ} (x : Fin a → K) (y : Fin b → K)
    (h : Fin.append x y = 0) : x = 0 ∧ y = 0 := by
  constructor
  · funext i
    have := congrFun h (Fin.castAdd b i)
    simpa using this
  · funext i
    have := congrFun h (Fin.natAdd a i)
    simpa using this

lemma pf_append_zero {K : Type*} [Field K] {a b : ℕ} :
    Fin.append (0 : Fin a → K) (0 : Fin b → K) = 0 := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [Fin.append_left]; rfl
  · rw [Fin.append_right]; rfl

lemma pf_exists_append {K : Type*} {a b : ℕ} (x : Fin (a + b) → K) :
    ∃ (x₁ : Fin a → K) (x₂ : Fin b → K), x = Fin.append x₁ x₂ :=
  ⟨fun i => x (Fin.castAdd b i), fun i => x (Fin.natAdd a i), (Fin.append_castAdd_natAdd).symm⟩

/-- Sums of `m` squares are "round": every value is a similarity factor. -/
def PfRound (K : Type*) [Field K] (m : ℕ) : Prop :=
  ∀ x : Fin m → K, ∃ S : (Fin m → K) → (Fin m → K), ∀ y, pfSq (S y) = pfSq x * pfSq y

lemma pfRound_one (K : Type*) [Field K] : PfRound K 1 := by
  intro x
  refine ⟨fun y => x 0 • y, fun y => ?_⟩
  rw [pfSq_smul]
  simp [pfSq]

lemma pfRound_double (K : Type*) [Field K] (m : ℕ) (h : PfRound K m) : PfRound K (m + m) := by
  intro x
  obtain ⟨x₁, x₂, rfl⟩ := pf_exists_append x
  obtain ⟨S₁, hS₁⟩ := h x₁
  obtain ⟨S₂, hS₂⟩ := h x₂
  rw [pfSq_append]
  by_cases hv : pfSq x₂ = 0
  · refine ⟨fun y => Fin.append (S₁ fun i => y (Fin.castAdd m i))
      (S₁ fun i => y (Fin.natAdd m i)), fun y => ?_⟩
    obtain ⟨y₁, y₂, rfl⟩ := pf_exists_append y
    simp only [Fin.append_left, Fin.append_right, pfSq_append, hS₁, hv]
    ring
  by_cases hu : pfSq x₁ = 0
  · refine ⟨fun y => Fin.append (S₂ fun i => y (Fin.natAdd m i))
      (S₂ fun i => y (Fin.castAdd m i)), fun y => ?_⟩
    obtain ⟨y₁, y₂, rfl⟩ := pf_exists_append y
    simp only [Fin.append_left, Fin.append_right, pfSq_append, hS₂, hu]
    ring
  refine ⟨fun y => Fin.append
      (S₁ ((fun i => y (Fin.castAdd m i)) -
        pfSq x₂ • ((pfSq x₁ * pfSq x₂)⁻¹ • S₁ (S₂ fun i => y (Fin.natAdd m i)))))
      (S₂ ((fun i => y (Fin.castAdd m i)) +
        pfSq x₁ • ((pfSq x₁ * pfSq x₂)⁻¹ • S₁ (S₂ fun i => y (Fin.natAdd m i))))), fun y => ?_⟩
  obtain ⟨y₁, y₂, rfl⟩ := pf_exists_append y
  simp only [Fin.append_left, Fin.append_right, pfSq_append, hS₁, hS₂]
  have hb := pfQ_binary (pfSq x₁) (pfSq x₂) (fun _ => 1) y₁
    ((pfSq x₁ * pfSq x₂)⁻¹ • S₁ (S₂ y₂))
  simp only [pfQ_one] at hb
  rw [hb, pfSq_smul, hS₁, hS₂]
  field_simp

/-- Pure subform property for sums of `m` squares: a nonzero sum `w` of `m - 1` squares
splits off as `⟨1, w⟩ ⊗ e`. -/
def PfB (K : Type*) [Field K] (m : ℕ) : Prop :=
  ∀ k, k + 1 = m → ∀ (w : K) (x : Fin k → K), w ≠ 0 → w = pfSq x →
    ∃ (r : ℕ) (e : Fin r → K) (J : (Fin r → K) → (Fin r → K) → (Fin m → K)), r + r = m ∧
      (∀ z₁ z₂, pfSq (J z₁ z₂) = pfQ e z₁ + w * pfQ e z₂) ∧
      (∀ z₁ z₂, J z₁ z₂ = 0 → z₁ = 0 ∧ z₂ = 0)

lemma pfB_one (K : Type*) [Field K] : PfB K 1 := by
  intro k hk w x hw hx
  obtain rfl : k = 0 := by omega
  exact absurd (by simp [hx, pfSq]) hw

lemma pfB_double (K : Type*) [Field K] (hreal : ∀ m (c : Fin m → K), pfSq c = 0 → c = 0)
    (m : ℕ) (hm : 0 < m) (hA : PfRound K m) (hB : PfB K m) : PfB K (m + m) := by
  intro k hk w x hw hx
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain rfl : k = m' + (m' + 1) := by omega
  obtain ⟨x₁, x₂, rfl⟩ := pf_exists_append x
  rw [pfSq_append] at hx
  obtain ⟨S, hS⟩ := hA x₂
  have hSker : pfSq x₂ ≠ 0 → ∀ z, S z = 0 → z = 0 := by
    intro hy z hz
    have := hS z
    rw [hz] at this
    have h0 : pfSq z = 0 := by
      have h1 : pfSq (0 : Fin (m' + 1) → K) = 0 := by simp [pfSq]
      rw [h1] at this
      exact (mul_eq_zero.mp this.symm).resolve_left hy
    exact hreal _ z h0
  by_cases hy : pfSq x₂ = 0
  · -- `w` is a sum of `m' ` squares: use the induction hypothesis on both halves
    rw [hy, add_zero] at hx
    obtain ⟨r, e, J, hr, hJ, hker⟩ := hB m' rfl w x₁ hw hx
    refine ⟨r + r, Fin.append e e, fun z₁ z₂ => Fin.append
      (J (fun i => z₁ (Fin.castAdd r i)) (fun i => z₂ (Fin.castAdd r i)))
      (J (fun i => z₁ (Fin.natAdd r i)) (fun i => z₂ (Fin.natAdd r i))), by omega, ?_, ?_⟩
    · intro z₁ z₂
      obtain ⟨a₁, a₂, rfl⟩ := pf_exists_append z₁
      obtain ⟨b₁, b₂, rfl⟩ := pf_exists_append z₂
      simp only [Fin.append_left, Fin.append_right, pfSq_append, pfQ_append, hJ]
      ring
    · intro z₁ z₂ h
      obtain ⟨a₁, a₂, rfl⟩ := pf_exists_append z₁
      obtain ⟨b₁, b₂, rfl⟩ := pf_exists_append z₂
      simp only [Fin.append_left, Fin.append_right] at h
      obtain ⟨h1, h2⟩ := pf_append_eq_zero _ _ h
      obtain ⟨ha1, hb1⟩ := hker _ _ h1
      obtain ⟨ha2, hb2⟩ := hker _ _ h2
      have ha1 : a₁ = 0 := ha1
      have ha2 : a₂ = 0 := ha2
      have hb1 : b₁ = 0 := hb1
      have hb2 : b₂ = 0 := hb2
      subst ha1 ha2 hb1 hb2
      exact ⟨pf_append_zero, pf_append_zero⟩
  by_cases hx' : pfSq x₁ = 0
  · -- `w` is a sum of `m' + 1` squares: use roundness
    rw [hx', zero_add] at hx
    refine ⟨m' + 1, fun _ => 1, fun z₁ z₂ => Fin.append z₁ (S z₂), rfl, ?_, ?_⟩
    · intro z₁ z₂
      rw [pfSq_append, hS, pfQ_one, pfQ_one, hx]
    · intro z₁ z₂ h
      obtain ⟨h1, h2⟩ := pf_append_eq_zero _ _ h
      exact ⟨h1, hSker hy z₂ h2⟩
  -- general case
  obtain ⟨r, e, J, hr, hJ, hker⟩ := hB m' rfl (pfSq x₁) x₁ hx' rfl
  refine ⟨r + r, Fin.append e (fun i => pfSq x₁ * pfSq x₂ * e i), fun z₁ z₂ => Fin.append
    (J (fun i => z₁ (Fin.castAdd r i))
      ((fun i => z₂ (Fin.castAdd r i)) - pfSq x₂ • (fun i => z₂ (Fin.natAdd r i))))
    (S (J ((fun i => z₂ (Fin.castAdd r i)) + pfSq x₁ • (fun i => z₂ (Fin.natAdd r i)))
      (fun i => z₁ (Fin.natAdd r i)))), by omega, ?_, ?_⟩
  · intro z₁ z₂
    obtain ⟨a₁, a₂, rfl⟩ := pf_exists_append z₁
    obtain ⟨b₁, b₂, rfl⟩ := pf_exists_append z₂
    simp only [Fin.append_left, Fin.append_right, pfSq_append, pfQ_append, hJ, hS,
      pfQ_mul_weights]
    have hb := pfQ_binary (pfSq x₁) (pfSq x₂) e b₁ b₂
    rw [hx]
    linear_combination hb
  · intro z₁ z₂ h
    obtain ⟨a₁, a₂, rfl⟩ := pf_exists_append z₁
    obtain ⟨b₁, b₂, rfl⟩ := pf_exists_append z₂
    simp only [Fin.append_left, Fin.append_right] at h
    obtain ⟨h1, h2⟩ := pf_append_eq_zero _ _ h
    obtain ⟨ha1, hb1⟩ := hker _ _ h1
    obtain ⟨hb2, ha2⟩ := hker _ _ (hSker hy _ h2)
    have ha1 : a₁ = 0 := ha1
    have ha2 : a₂ = 0 := ha2
    have hb1 : b₁ - pfSq x₂ • b₂ = 0 := hb1
    have hb2 : b₁ + pfSq x₁ • b₂ = 0 := hb2
    have hb2z : b₂ = 0 := by
      have : (pfSq x₁ + pfSq x₂) • b₂ = 0 := by
        funext i
        have e1 := congrFun hb1 i
        have e2 := congrFun hb2 i
        simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e1 e2 ⊢
        linear_combination e2 - e1
      exact (smul_eq_zero.mp this).resolve_left (hx ▸ hw)
    have hb1z : b₁ = 0 := by rw [hb2z, smul_zero, sub_zero] at hb1; exact hb1
    subst ha1 ha2 hb1z hb2z
    exact ⟨pf_append_zero, pf_append_zero⟩

lemma pfRound_pow (K : Type*) [Field K] (n : ℕ) : PfRound K (2 ^ n) := by
  induction n with
  | zero => exact pfRound_one K
  | succ n ih =>
    have : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by ring
    rw [this]; exact pfRound_double K _ ih

lemma pfB_pow (K : Type*) [Field K] (hreal : ∀ m (c : Fin m → K), pfSq c = 0 → c = 0) (n : ℕ) :
    PfB K (2 ^ n) := by
  induction n with
  | zero => exact pfB_one K
  | succ n ih =>
    have : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by ring
    rw [this]; exact pfB_double K hreal _ (by positivity) (pfRound_pow K n) ih

/-- The Tsen–Lang property used below: a diagonal quadratic form with weights `a j + i b j`
in `M` variables has a nontrivial zero `p + i q` over `K(i)`; written over `K`. -/
def PfTL (K : Type*) [Field K] (M : ℕ) : Prop :=
  ∀ a b : Fin M → K, ∃ p q : Fin M → K, (p ≠ 0 ∨ q ≠ 0) ∧
    ∑ j, (a j * (p j ^ 2 - q j ^ 2) - 2 * b j * p j * q j) = 0 ∧
    ∑ j, (b j * (p j ^ 2 - q j ^ 2) + 2 * a j * p j * q j) = 0

lemma pf_twist {K : Type*} [Field K] {m : ℕ} (c p q : Fin m → K) (t₁ t₂ : K) :
    pfQ c (t₁ • p + t₂ • q) - pfQ c (t₁ • q - t₂ • p) =
        (t₁ ^ 2 - t₂ ^ 2) * (pfQ c p - pfQ c q) + 2 * t₁ * t₂ * (2 * pfB c p q) ∧
      2 * pfB c (t₁ • p + t₂ • q) (t₁ • q - t₂ • p) =
        (t₁ ^ 2 - t₂ ^ 2) * (2 * pfB c p q) - 2 * t₁ * t₂ * (pfQ c p - pfQ c q) := by
  constructor
  · simp only [pfQ, pfB, Finset.mul_sum, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  · simp only [pfQ, pfB, Finset.mul_sum, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)

/-- From the Tsen–Lang property: a vector `(p', q')` on which `(g₁ + i g₂) c(p' + i q')` is
"real". -/
lemma pf_real_value {K : Type*} [Field K]
    (hreal2 : ∀ t₁ t₂ : K, t₁ ^ 2 + t₂ ^ 2 = 0 → t₁ = 0 ∧ t₂ = 0) {m : ℕ}
    (hTL : PfTL K (m + 1)) (c : Fin m → K) (g₁ g₂ : K) (hN : g₁ ^ 2 + g₂ ^ 2 ≠ 0) :
    ∃ p' q' : Fin m → K, (p' ≠ 0 ∨ q' ≠ 0) ∧
      g₂ * (pfQ c p' - pfQ c q') + g₁ * (2 * pfB c p' q') = 0 := by
  obtain ⟨p, q, hne, h1, h2⟩ := hTL (Fin.snoc c (-g₁)) (Fin.snoc (fun _ => 0) g₂)
  rw [Fin.sum_univ_castSucc] at h1 h2
  simp only [Fin.snoc_castSucc, Fin.snoc_last] at h1 h2
  obtain ⟨p₀, hp₀⟩ : ∃ p₀ : Fin m → K, p₀ = fun i => p (Fin.castSucc i) := ⟨_, rfl⟩
  obtain ⟨q₀, hq₀⟩ : ∃ q₀ : Fin m → K, q₀ = fun i => q (Fin.castSucc i) := ⟨_, rfl⟩
  obtain ⟨t₁, ht₁⟩ : ∃ t₁ : K, t₁ = p (Fin.last m) := ⟨_, rfl⟩
  obtain ⟨t₂, ht₂⟩ : ∃ t₂ : K, t₂ = q (Fin.last m) := ⟨_, rfl⟩
  have hU : pfQ c p₀ - pfQ c q₀ = g₁ * (t₁ ^ 2 - t₂ ^ 2) + g₂ * (2 * t₁ * t₂) := by
    have : pfQ c p₀ - pfQ c q₀ =
        ∑ i : Fin m, (c i * (p (Fin.castSucc i) ^ 2 - q (Fin.castSucc i) ^ 2) -
          2 * 0 * p (Fin.castSucc i) * q (Fin.castSucc i)) := by
      rw [hp₀, hq₀]
      simp only [pfQ, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [this, ht₁, ht₂]
    linear_combination h1
  have hW : 2 * pfB c p₀ q₀ = -g₂ * (t₁ ^ 2 - t₂ ^ 2) + g₁ * (2 * t₁ * t₂) := by
    have : 2 * pfB c p₀ q₀ =
        ∑ i : Fin m, (0 * (p (Fin.castSucc i) ^ 2 - q (Fin.castSucc i) ^ 2) +
          2 * c i * p (Fin.castSucc i) * q (Fin.castSucc i)) := by
      rw [hp₀, hq₀]
      simp only [pfB, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [this, ht₁, ht₂]
    linear_combination h2
  by_cases ht : t₁ = 0 ∧ t₂ = 0
  · obtain ⟨ht10, ht20⟩ := ht
    refine ⟨p₀, q₀, ?_, ?_⟩
    · rcases hne with hp | hq
      · left
        intro h0; apply hp
        funext j
        refine Fin.lastCases ?_ (fun i => ?_) j
        · rw [← ht₁, ht10]; rfl
        · have := congrFun h0 i
          rw [hp₀] at this; exact this
      · right
        intro h0; apply hq
        funext j
        refine Fin.lastCases ?_ (fun i => ?_) j
        · rw [← ht₂, ht20]; rfl
        · have := congrFun h0 i
          rw [hq₀] at this; exact this
    · rw [hU, hW, ht10, ht20]; ring
  · obtain ⟨e1, e2⟩ := pf_twist c p₀ q₀ t₁ t₂
    refine ⟨t₁ • p₀ + t₂ • q₀, t₁ • q₀ - t₂ • p₀, ?_, ?_⟩
    · by_contra hcon
      push Not at hcon
      obtain ⟨hp', hq'⟩ := hcon
      have hT : t₁ ^ 2 + t₂ ^ 2 ≠ 0 := fun h0 => ht (hreal2 t₁ t₂ h0)
      have hp0 : p₀ = 0 := by
        funext i
        have a1 := congrFun hp' i
        have a2 := congrFun hq' i
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
          at a1 a2 ⊢
        have : (t₁ ^ 2 + t₂ ^ 2) * p₀ i = 0 := by linear_combination t₁ * a1 - t₂ * a2
        exact (mul_eq_zero.mp this).resolve_left hT
      have hq0 : q₀ = 0 := by
        funext i
        have a1 := congrFun hp' i
        have a2 := congrFun hq' i
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
          at a1 a2 ⊢
        have : (t₁ ^ 2 + t₂ ^ 2) * q₀ i = 0 := by linear_combination t₂ * a1 + t₁ * a2
        exact (mul_eq_zero.mp this).resolve_left hT
      rw [hp0, hq0] at hU hW
      have z1 : pfQ c (0 : Fin m → K) = 0 := by simp [pfQ]
      have z2 : pfB c (0 : Fin m → K) 0 = 0 := by simp [pfB]
      rw [z1, sub_zero] at hU
      rw [z2, mul_zero] at hW
      have ha : (g₁ ^ 2 + g₂ ^ 2) * (t₁ ^ 2 - t₂ ^ 2) = 0 := by
        linear_combination (-g₁) * hU + g₂ * hW
      have hb : (g₁ ^ 2 + g₂ ^ 2) * (2 * t₁ * t₂) = 0 := by
        linear_combination (-g₂) * hU - g₁ * hW
      have ha' := (mul_eq_zero.mp ha).resolve_left hN
      have hb' := (mul_eq_zero.mp hb).resolve_left hN
      have : (t₁ ^ 2 + t₂ ^ 2) ^ 2 = 0 := by
        linear_combination (t₁ ^ 2 - t₂ ^ 2) * ha' + (2 * t₁ * t₂) * hb'
      exact hT (pow_eq_zero_iff (two_ne_zero) |>.mp this)
    · rw [e1, e2, hU, hW]; ring

/-- From the Tsen–Lang property: `c ⊗ ⟨1, -(g₁² + g₂²)⟩` is isotropic. -/
lemma pf_norm_isotropic {K : Type*} [Field K]
    (hreal2 : ∀ t₁ t₂ : K, t₁ ^ 2 + t₂ ^ 2 = 0 → t₁ = 0 ∧ t₂ = 0) {m : ℕ} (hm : 0 < m)
    (hTL : PfTL K (m + 1)) (c : Fin m → K) (g₁ g₂ : K) (hN : g₁ ^ 2 + g₂ ^ 2 ≠ 0) :
    ∃ P Q : Fin m → K, (P ≠ 0 ∨ Q ≠ 0) ∧ pfQ c P = (g₁ ^ 2 + g₂ ^ 2) * pfQ c Q := by
  by_cases hg : g₂ = 0
  · refine ⟨g₁ • Pi.single ⟨0, hm⟩ 1, Pi.single ⟨0, hm⟩ 1, Or.inr ?_, ?_⟩
    · intro h0
      have := congrFun h0 ⟨0, hm⟩
      simp at this
    · rw [pfQ_smul, hg]; ring
  · obtain ⟨p', q', hne, h⟩ := pf_real_value hreal2 hTL c g₁ g₂ hN
    refine ⟨p' + (g₁ / g₂) • q', g₂⁻¹ • q', ?_, ?_⟩
    · by_contra hcon
      push Not at hcon
      obtain ⟨hP, hQ⟩ := hcon
      have hq' : q' = 0 := (smul_eq_zero.mp hQ).resolve_left (inv_ne_zero hg)
      rw [hq', smul_zero, add_zero] at hP
      rcases hne with h1 | h1
      · exact h1 hP
      · exact h1 hq'
    · rw [pfQ_add_smul, pfQ_smul]
      field_simp
      linear_combination g₂ * h

/-- The descent step: a square plus a sum of `m` squares is a sum of `m` squares. -/
theorem pf_descent_step {K : Type*} [Field K]
    (hreal : ∀ m (c : Fin m → K), pfSq c = 0 → c = 0) (m' : ℕ)
    (hA : PfRound K (m' + 1)) (hB : PfB K (m' + 1)) (hTL : PfTL K (m' + 1 + 1))
    (s : K) (f : Fin (m' + 1) → K) : ∃ f' : Fin (m' + 1) → K, s ^ 2 + pfSq f = pfSq f' := by
  have hreal2 : ∀ t₁ t₂ : K, t₁ ^ 2 + t₂ ^ 2 = 0 → t₁ = 0 ∧ t₂ = 0 := by
    intro t₁ t₂ h
    have := hreal 2 ![t₁, t₂] (by simpa [pfSq, Fin.sum_univ_two] using h)
    exact ⟨by simpa using congrFun this 0, by simpa using congrFun this 1⟩
  -- quotients of values are values
  have hquot : ∀ z₁ z₂ : Fin (m' + 1) → K, pfSq z₂ ≠ 0 →
      ∃ f' : Fin (m' + 1) → K, pfSq z₁ / pfSq z₂ = pfSq f' := by
    intro z₁ z₂ h2
    obtain ⟨S, hS⟩ := hA z₁
    refine ⟨(pfSq z₂)⁻¹ • S z₂, ?_⟩
    rw [pfSq_smul, hS]
    field_simp
  obtain ⟨x, hx⟩ : ∃ x : Fin m' → K, x = fun i => f i.succ := ⟨_, rfl⟩
  have hf : pfSq f = f 0 ^ 2 + pfSq x := by
    rw [hx]; simp [pfSq, Fin.sum_univ_succ]
  by_cases hN : s ^ 2 + f 0 ^ 2 = 0
  · refine ⟨f, ?_⟩
    rw [(hreal2 _ _ hN).1]; ring
  by_cases hw : pfSq x = 0
  · obtain ⟨P, Q, hne, h⟩ := pf_norm_isotropic hreal2 (Nat.succ_pos m') hTL (fun _ => 1)
      s (f 0) hN
    rw [pfQ_one, pfQ_one] at h
    have hQ : pfSq Q ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at h
      rcases hne with h1 | h1
      · exact h1 (hreal _ P h)
      · exact h1 (hreal _ Q h0)
    obtain ⟨f', hf'⟩ := hquot P Q hQ
    refine ⟨f', ?_⟩
    rw [← hf', hf, hw, h]
    field_simp
    ring
  · obtain ⟨r, e, J, hr, hJ, hker⟩ := hB m' rfl (pfSq x) x hw rfl
    obtain ⟨β, hβ⟩ : ∃ β : K, β = s ^ 2 + f 0 ^ 2 + pfSq x := ⟨_, rfl⟩
    rw [← hr] at hTL
    have hrpos : 0 < r + r := by omega
    obtain ⟨P, Q, hne, h⟩ := pf_norm_isotropic hreal2 hrpos hTL
      (Fin.append e (fun i => (-(pfSq x * β)) * e i)) s (f 0) hN
    obtain ⟨P₁, P₂, rfl⟩ := pf_exists_append P
    obtain ⟨Q₁, Q₂, rfl⟩ := pf_exists_append Q
    rw [pfQ_append, pfQ_append, pfQ_mul_weights, pfQ_mul_weights] at h
    have hb := pfQ_binary (pfSq x) (-β) e Q₁ Q₂
    have key : pfSq (J P₁ (Q₁ - (-β) • Q₂)) = β * pfSq (J (Q₁ + pfSq x • Q₂) P₂) := by
      rw [hJ, hJ]
      linear_combination h + hb - (pfQ e Q₁ - pfSq x * β * pfQ e Q₂) * hβ
    have hden : pfSq (J (Q₁ + pfSq x • Q₂) P₂) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at key
      obtain ⟨a1, a2⟩ := hker _ _ (hreal _ _ h0)
      obtain ⟨a3, a4⟩ := hker _ _ (hreal _ _ key)
      have hQ2 : Q₂ = 0 := by
        have : (s ^ 2 + f 0 ^ 2) • Q₂ = 0 := by
          funext i
          have e1 := congrFun a1 i
          have e2 := congrFun a4 i
          simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
            at e1 e2 ⊢
          rw [hβ] at e2
          linear_combination e2 - e1
        exact (smul_eq_zero.mp this).resolve_left hN
      have hQ1 : Q₁ = 0 := by rw [hQ2, smul_zero, add_zero] at a1; exact a1
      rw [a2, a3, hQ1, hQ2] at hne
      rcases hne with h1 | h1 <;> exact h1 pf_append_zero
    obtain ⟨f', hf'⟩ := hquot _ _ hden
    refine ⟨f', ?_⟩
    rw [← hf', key, hf, hβ]
    field_simp
    ring

/-- Sums of squares are sums of `2 ^ n` squares, given the Tsen–Lang property. -/
theorem pf_pythagoras {K : Type*} [Field K]
    (hreal : ∀ m (c : Fin m → K), pfSq c = 0 → c = 0) (n : ℕ) (hTL : PfTL K (2 ^ n + 1))
    (a : K) (ha : IsSumSq a) : ∃ f : Fin (2 ^ n) → K, a = ∑ i, f i * f i := by
  obtain ⟨m', hm'⟩ : ∃ m', 2 ^ n = m' + 1 := ⟨2 ^ n - 1, by have := Nat.one_le_two_pow (n := n); omega⟩
  have hA := pfRound_pow K n
  have hB := pfB_pow K hreal n
  rw [hm'] at hA hB hTL ⊢
  have main : ∃ f : Fin (m' + 1) → K, a = pfSq f := by
    induction ha with
    | zero => exact ⟨0, by simp [pfSq]⟩
    | sq_add b hs ih =>
      obtain ⟨f, rfl⟩ := ih
      obtain ⟨f', hf'⟩ := pf_descent_step hreal m' hA hB hTL b f
      exact ⟨f', by rw [← hf']; ring⟩
  obtain ⟨f, hf⟩ := main
  exact ⟨f, by rw [hf, pfSq]; exact Finset.sum_congr rfl (fun i _ => sq _)⟩

/-- P1 for an arbitrary finite set of variables. -/
theorem pf_common_zero' {k : Type*} [Field k] [IsAlgClosed k] {σ : Type*} [Fintype σ] {r : ℕ}
    (hr : r < Fintype.card σ) (f : Fin r → MvPolynomial σ k)
    (hf : ∀ i, MvPolynomial.eval 0 (f i) = 0) :
    ∃ x : σ → k, x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (f i) = 0 := by
  classical
  obtain ⟨e⟩ : Nonempty (σ ≃ Fin (Fintype.card σ)) := ⟨Fintype.equivFin σ⟩
  obtain ⟨x, hx, hx'⟩ := pf_common_zero hr (fun i => MvPolynomial.rename e (f i)) (fun i => by
    rw [MvPolynomial.eval_rename]; exact hf i)
  refine ⟨x ∘ e, ?_, fun i => ?_⟩
  · intro h0; apply hx; funext j
    have := congrFun h0 (e.symm j)
    simpa using this
  · have := hx' i
    rwa [MvPolynomial.eval_rename] at this

lemma pf_pow_aux (b c : ℕ) : ∀ n : ℕ, (b + c) ^ n ≤ b ^ n + n * c * (b + c) ^ (n - 1)
  | 0 => by simp
  | n + 1 => by
    have ih := pf_pow_aux b c n
    have h1 : b * (b + c) ^ (n - 1) * n ≤ (b + c) ^ n * n := by
      rcases n with _ | k
      · simp
      · simp only [Nat.add_sub_cancel]
        have : b * (b + c) ^ k ≤ (b + c) ^ (k + 1) := by
          rw [pow_succ']; exact Nat.mul_le_mul_right _ (Nat.le_add_right b c)
        exact Nat.mul_le_mul_right _ this
    calc (b + c) ^ (n + 1) = b * (b + c) ^ n + c * (b + c) ^ n := by ring
      _ ≤ b * (b ^ n + n * c * (b + c) ^ (n - 1)) + c * (b + c) ^ n := by gcongr
      _ = b ^ (n + 1) + c * (b * (b + c) ^ (n - 1) * n) + c * (b + c) ^ n := by ring
      _ ≤ b ^ (n + 1) + c * ((b + c) ^ n * n) + c * (b + c) ^ n := by gcongr
      _ = b ^ (n + 1) + (n + 1) * c * (b + c) ^ (n + 1 - 1) := by
        simp only [Nat.add_sub_cancel]; ring

lemma pf_exists_T (n c : ℕ) : ∃ T : ℕ, 0 < T ∧ (2 * T + c) ^ n < (2 ^ n + 1) * T ^ n := by
  rcases n with _ | k
  · exact ⟨1, one_pos, by simp⟩
  · obtain ⟨T, hT⟩ : ∃ T, T = (k + 1) * c * (2 + c) ^ k + 1 := ⟨_, rfl⟩
    have hT1 : 1 ≤ T := by omega
    refine ⟨T, hT1, ?_⟩
    have h1 := pf_pow_aux (2 * T) c (k + 1)
    simp only [Nat.add_sub_cancel] at h1
    have h2 : (2 * T + c) ^ k ≤ (2 + c) ^ k * T ^ k := by
      rw [← mul_pow]; apply Nat.pow_le_pow_left; nlinarith
    have h3 : (k + 1) * c * (2 + c) ^ k < T := by omega
    have hTk : 0 < T ^ k := by positivity
    calc (2 * T + c) ^ (k + 1) ≤ (2 * T) ^ (k + 1) + (k + 1) * c * (2 * T + c) ^ k := h1
      _ ≤ (2 * T) ^ (k + 1) + (k + 1) * c * ((2 + c) ^ k * T ^ k) := by gcongr
      _ = 2 ^ (k + 1) * T ^ (k + 1) + ((k + 1) * c * (2 + c) ^ k) * T ^ k := by ring
      _ < 2 ^ (k + 1) * T ^ (k + 1) + T * T ^ k :=
        Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right h3 hTk) _
      _ = (2 ^ (k + 1) + 1) * T ^ (k + 1) := by ring

/-- The exponent vector attached to a box index. -/
noncomputable def pfMon {n T : ℕ} (s : Fin n → Fin T) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (s i : ℕ))

lemma pfMon_apply {n T : ℕ} (s : Fin n → Fin T) (i : Fin n) : pfMon s i = s i := by
  simp [pfMon]

lemma pfMon_injective {n T : ℕ} : Function.Injective (pfMon (n := n) (T := T)) := by
  intro s s' h
  funext i
  have := DFunLike.congr_fun h i
  rw [pfMon_apply, pfMon_apply] at this
  exact Fin.ext this

/-- The polynomial with prescribed coefficients on the box. -/
noncomputable def pfBoxPoly {R : Type*} [CommSemiring R] {n T : ℕ} (a : (Fin n → Fin T) → R) :
    MvPolynomial (Fin n) R :=
  ∑ s, MvPolynomial.monomial (pfMon s) (a s)

lemma pfBoxPoly_coeff {R : Type*} [CommSemiring R] {n T : ℕ} (a : (Fin n → Fin T) → R)
    (s₀ : Fin n → Fin T) : MvPolynomial.coeff (pfMon s₀) (pfBoxPoly a) = a s₀ := by
  classical
  rw [pfBoxPoly, MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single s₀]
  · simp
  · intro s _ hs
    rw [MvPolynomial.coeff_monomial, if_neg (fun h => hs (pfMon_injective h))]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma pfBoxPoly_map {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S) {n T : ℕ}
    (a : (Fin n → Fin T) → R) :
    MvPolynomial.map φ (pfBoxPoly a) = pfBoxPoly (fun s => φ (a s)) := by
  simp [pfBoxPoly, map_sum, MvPolynomial.map_monomial]

lemma pfBoxPoly_degreeOf {R : Type*} [CommSemiring R] {n T : ℕ} (a : (Fin n → Fin T) → R)
    (i : Fin n) : MvPolynomial.degreeOf i (pfBoxPoly a) ≤ T - 1 := by
  classical
  rw [pfBoxPoly]
  refine (MvPolynomial.degreeOf_sum_le i _ _).trans (Finset.sup_le fun s _ => ?_)
  rw [MvPolynomial.degreeOf_le_iff]
  intro m hm
  have := MvPolynomial.support_monomial_subset hm
  rw [Finset.mem_singleton] at this
  rw [this, pfMon_apply]
  have := (s i).2
  omega

open MvPolynomial in
/-- Tsen–Lang over `ℂ[X₁, …, Xₙ]` for diagonal quadratic forms in `M > 2 ^ n` variables. -/
theorem pf_complex_zero (n M : ℕ) (hM : 2 ^ n < M) (Cc : Fin M → MvPolynomial (Fin n) ℂ) :
    ∃ (T : ℕ) (z : Fin M × (Fin n → Fin T) → ℂ), z ≠ 0 ∧
      ∑ j, Cc j * (pfBoxPoly fun s => z (j, s)) ^ 2 = 0 := by
  classical
  obtain ⟨c, hc⟩ : ∃ c : ℕ, ∀ j i, degreeOf i (Cc j) ≤ c := by
    refine ⟨∑ j, ∑ i, degreeOf i (Cc j), fun j i => ?_⟩
    exact (Finset.single_le_sum (f := fun i => degreeOf i (Cc j)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)).trans
      (Finset.single_le_sum (f := fun j => ∑ i, degreeOf i (Cc j)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j))
  obtain ⟨T, hT0, hT⟩ := pf_exists_T n c
  obtain ⟨G, hG⟩ : ∃ G : MvPolynomial (Fin n) (MvPolynomial (Fin M × (Fin n → Fin T)) ℂ),
      G = ∑ j, map C (Cc j) * (pfBoxPoly fun s => X (j, s)) ^ 2 := ⟨_, rfl⟩
  have hφ : ∀ z : Fin M × (Fin n → Fin T) → ℂ,
      map (eval z) G = ∑ j, Cc j * (pfBoxPoly fun s => z (j, s)) ^ 2 := by
    intro z
    rw [hG, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_pow, MvPolynomial.map_map, pfBoxPoly_map]
    have h1 : (eval z).comp C = RingHom.id ℂ := by ext a; simp
    rw [h1, MvPolynomial.map_id]
    simp
  have hdeg : ∀ i, degreeOf i G ≤ c + 2 * (T - 1) := by
    intro i
    rw [hG]
    refine (degreeOf_sum_le i _ _).trans (Finset.sup_le fun j _ => ?_)
    refine (degreeOf_mul_le i _ _).trans (Nat.add_le_add ?_ ?_)
    · rw [degreeOf_le_iff]
      intro m hm
      exact (monomial_le_degreeOf i (support_map_subset _ _ hm)).trans (hc j i)
    · exact (degreeOf_pow_le i _ 2).trans (Nat.mul_le_mul_left 2 (pfBoxPoly_degreeOf _ i))
  have hcard : G.support.card ≤ (2 * T + c) ^ n := by
    have := Finset.card_le_card_of_injOn (s := G.support)
      (t := Fintype.piFinset (fun _ : Fin n => Finset.range (2 * T + c)))
      (fun ν i => ν i) (by
        intro ν hν
        rw [Finset.mem_coe, Fintype.mem_piFinset]
        intro i
        rw [Finset.mem_range]
        have := (monomial_le_degreeOf i (Finset.mem_coe.mp hν)).trans (hdeg i)
        show ν i < 2 * T + c
        omega) (by
        intro ν _ ν' _ h
        exact DFunLike.coe_injective h)
    simpa [Fintype.card_piFinset] using this
  have hr : G.support.card < Fintype.card (Fin M × (Fin n → Fin T)) := by
    have h1 : Fintype.card (Fin M × (Fin n → Fin T)) = M * T ^ n := by simp
    rw [h1]
    calc G.support.card ≤ (2 * T + c) ^ n := hcard
      _ < (2 ^ n + 1) * T ^ n := hT
      _ ≤ M * T ^ n := Nat.mul_le_mul_right _ hM
  have hf : ∀ i : Fin G.support.card,
      eval (0 : Fin M × (Fin n → Fin T) → ℂ) (coeff (G.support.equivFin.symm i).1 G) = 0 := by
    intro i
    rw [← coeff_map, hφ]
    simp [pfBoxPoly]
  obtain ⟨x, hx, hx'⟩ := pf_common_zero' hr
    (fun i => coeff (G.support.equivFin.symm i).1 G) hf
  refine ⟨T, x, hx, ?_⟩
  rw [← hφ]
  ext ν
  rw [coeff_map, coeff_zero]
  by_cases hν : ν ∈ G.support
  · have := hx' (G.support.equivFin ⟨ν, hν⟩)
    simpa using this
  · rw [notMem_support_iff.mp hν, map_zero]

open MvPolynomial in
/-- Tsen–Lang for `ℝ[X₁, …, Xₙ]`, written with real and imaginary parts. -/
theorem pf_real_zero (n M : ℕ) (hM : 2 ^ n < M) (A B : Fin M → MvPolynomial (Fin n) ℝ) :
    ∃ p q : Fin M → MvPolynomial (Fin n) ℝ, (p ≠ 0 ∨ q ≠ 0) ∧
      ∑ j, (A j * (p j ^ 2 - q j ^ 2) - 2 * B j * p j * q j) = 0 ∧
      ∑ j, (B j * (p j ^ 2 - q j ^ 2) + 2 * A j * p j * q j) = 0 := by
  classical
  obtain ⟨mm, hmm⟩ : ∃ mm : MvPolynomial (Fin n) ℝ →+* MvPolynomial (Fin n) ℂ,
      mm = map Complex.ofRealHom := ⟨_, rfl⟩
  obtain ⟨T, z, hz, hsum⟩ := pf_complex_zero n M hM
    (fun j => mm (A j) + C Complex.I * mm (B j))
  obtain ⟨p, hp⟩ : ∃ p : Fin M → MvPolynomial (Fin n) ℝ,
      p = fun j => pfBoxPoly fun s => (z (j, s)).re := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : Fin M → MvPolynomial (Fin n) ℝ,
      q = fun j => pfBoxPoly fun s => (z (j, s)).im := ⟨_, rfl⟩
  have hζ : ∀ j, (pfBoxPoly fun s => z (j, s)) = mm (p j) + C Complex.I * mm (q j) := by
    intro j
    rw [hp, hq, hmm]
    simp only [pfBoxPoly_map]
    simp only [pfBoxPoly, Finset.mul_sum, C_mul_monomial, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← map_add]
    congr 1
    first
      | exact (Complex.re_add_im _).symm
      | (rw [mul_comm]; exact (Complex.re_add_im _).symm)
  have hI : (C Complex.I : MvPolynomial (Fin n) ℂ) * C Complex.I = -1 := by
    rw [← C_mul, Complex.I_mul_I]; simp
  have key : mm (∑ j, (A j * (p j ^ 2 - q j ^ 2) - 2 * B j * p j * q j)) +
      C Complex.I * mm (∑ j, (B j * (p j ^ 2 - q j ^ 2) + 2 * A j * p j * q j)) = 0 := by
    rw [map_sum, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← hsum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, hζ]
    linear_combination (-(mm (A j) * mm (q j) ^ 2 + C Complex.I * mm (B j) * mm (q j) ^ 2 +
      2 * mm (B j) * mm (p j) * mm (q j))) * hI
  have hE : ∀ E1 E2 : MvPolynomial (Fin n) ℝ, mm E1 + C Complex.I * mm E2 = 0 →
      E1 = 0 ∧ E2 = 0 := by
    intro E1 E2 h
    have hν : ∀ ν, coeff ν E1 = 0 ∧ coeff ν E2 = 0 := by
      intro ν
      have := congrArg (coeff ν) h
      rw [hmm] at this
      simp only [coeff_add, coeff_map, coeff_C_mul, coeff_zero] at this
      have h2 := Complex.ext_iff.mp this
      simpa using h2
    exact ⟨MvPolynomial.ext _ _ fun ν => by simpa using (hν ν).1,
      MvPolynomial.ext _ _ fun ν => by simpa using (hν ν).2⟩
  obtain ⟨e1, e2⟩ := hE _ _ key
  refine ⟨p, q, ?_, e1, e2⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hp0, hq0⟩ := hcon
  apply hz
  funext ⟨j, s⟩
  have h1 := congrArg (coeff (pfMon s)) (congrFun hp0 j)
  have h2 := congrArg (coeff (pfMon s)) (congrFun hq0 j)
  rw [hp] at h1
  rw [hq] at h2
  simp only [pfBoxPoly_coeff, Pi.zero_apply, coeff_zero] at h1 h2
  exact Complex.ext h1 h2

/-- Tsen–Lang property for `ℝ(X₁, …, Xₙ)`. -/
theorem pf_TL (n M : ℕ) (hM : 2 ^ n < M) :
    PfTL (FractionRing (MvPolynomial (Fin n) ℝ)) M := by
  classical
  intro a b
  obtain ⟨D, hD⟩ := IsLocalization.exist_integer_multiples
    (nonZeroDivisors (MvPolynomial (Fin n) ℝ)) Finset.univ (Sum.elim a b)
  have hA : ∀ j, ∃ A : MvPolynomial (Fin n) ℝ,
      algebraMap _ (FractionRing (MvPolynomial (Fin n) ℝ)) A =
        algebraMap _ (FractionRing (MvPolynomial (Fin n) ℝ)) (D : MvPolynomial (Fin n) ℝ) *
          a j := fun j => by
    obtain ⟨A, hA⟩ := hD (Sum.inl j) (Finset.mem_univ _)
    exact ⟨A, by rw [hA, Algebra.smul_def]; rfl⟩
  have hB : ∀ j, ∃ B : MvPolynomial (Fin n) ℝ,
      algebraMap _ (FractionRing (MvPolynomial (Fin n) ℝ)) B =
        algebraMap _ (FractionRing (MvPolynomial (Fin n) ℝ)) (D : MvPolynomial (Fin n) ℝ) *
          b j := fun j => by
    obtain ⟨B, hB⟩ := hD (Sum.inr j) (Finset.mem_univ _)
    exact ⟨B, by rw [hB, Algebra.smul_def]; rfl⟩
  choose A hA using hA
  choose B hB using hB
  obtain ⟨p, q, hne, h1, h2⟩ := pf_real_zero n M hM A B
  have hinj := IsFractionRing.injective (MvPolynomial (Fin n) ℝ)
    (FractionRing (MvPolynomial (Fin n) ℝ))
  have hD0 : algebraMap _ (FractionRing (MvPolynomial (Fin n) ℝ))
      (D : MvPolynomial (Fin n) ℝ) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hinj]
    exact nonZeroDivisors.coe_ne_zero D
  refine ⟨fun j => algebraMap _ _ (p j), fun j => algebraMap _ _ (q j), ?_, ?_, ?_⟩
  · rcases hne with h | h
    · left; intro h0; apply h; funext j
      exact hinj ((congrFun h0 j).trans (map_zero _).symm)
    · right; intro h0; apply h; funext j
      exact hinj ((congrFun h0 j).trans (map_zero _).symm)
  · have := congrArg (algebraMap _ (FractionRing (MvPolynomial (Fin n) ℝ))) h1
    simp only [map_sum, map_sub, map_add, map_mul, map_pow, map_ofNat, hA, hB, map_zero] at this
    refine (mul_eq_zero.mp ?_).resolve_left hD0
    rw [Finset.mul_sum, ← this]
    exact Finset.sum_congr rfl fun j _ => by ring
  · have := congrArg (algebraMap _ (FractionRing (MvPolynomial (Fin n) ℝ))) h2
    simp only [map_sum, map_sub, map_add, map_mul, map_pow, map_ofNat, hA, hB, map_zero] at this
    refine (mul_eq_zero.mp ?_).resolve_left hD0
    rw [Finset.mul_sum, ← this]
    exact Finset.sum_congr rfl fun j _ => by ring

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

/--
**Pfister's theorem**: every sum of squares in $\mathbb{R}(X_1, \dots, X_n)$ is a sum of $2^n$
squares [Pfister1995, p. 95]; this is Corollary 1 of Theorem 2 in [Pfister1971]. For positive
semidefinite polynomials it is [Pfister1967, Theorem 1], the quantitative refinement of Artin's
theorem `Hilbert17.hilbert_17th_problem` in `FormalConjectures/HilbertProblems/17.lean`.
-/
@[category research solved, AMS 11 12 14]
theorem pfister_problem.variants.upper_bound (n : ℕ) :
    2 ^ n ∈ pythagorasBounds (MvRatFunc (Fin n) ℝ) := by
  intro a ha
  exact pf_pythagoras (fun _ c hc => pf_aniso_ratFunc c hc) n (pf_TL n _ (Nat.lt_succ_self _)) a ha

/--
**Cassels' theorem** [Cassels1964], as quoted in Problem 1 of [Pfister1971, §4]:
$1 + X_1^2 + \dots + X_n^2$ is not a sum of $n$ squares in $\mathbb{R}(X_1, \dots, X_n)$.
-/
@[category research solved, AMS 11 12 14]
theorem pfister_problem.variants.cassels (n : ℕ) :
    ¬IsSumSqOfLength n (algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ)
      (1 + ∑ i, MvPolynomial.X i * MvPolynomial.X i)) := by
  sorry

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
