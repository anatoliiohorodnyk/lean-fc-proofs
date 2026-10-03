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
# Kaplansky's problem on the values of the $u$-invariant

The $u$-invariant $u(F)$ of a field $F$ is the largest dimension of an anisotropic quadratic form
over $F$, or $\infty$ if there is no largest one; that is, $u(F) = n$ exactly when
`IsGreatest (QuadraticForm.anisotropicDims F) n`. Following [Kaplansky1953] and
[MerkurjevParimala2025, §5.1], all fields are of characteristic not $2$.

Kaplansky introduced the invariant (his $C(F)$) in [Kaplansky1953, p. 201], proved that $u(F) \ne 3$
(his Theorem 2), observed that every power of $2$ occurs (his Theorem 3 gives
$u(F((t))) = 2u(F)$), and conjectured that $u(F)$ is a power of $2$ whenever it is finite
[Kaplansky1953, p. 202]. It is classical that $u(F) \notin \{3, 5, 7\}$
[Lam2005, Proposition XI.6.8], [EKM2008, Corollary 36.4]. Merkurjev disproved Kaplansky's
conjecture with a field of $u$-invariant $6$ [Merkurjev1989] and then showed that every positive
even integer is a $u$-invariant [Merkurjev1991]. Izhboldin constructed a field of $u$-invariant
$9$ [Izhboldin2001], and Vishik fields of $u$-invariant $2^r + 1$ for every $r \ge 3$
[Vishik2009]. A 2026 preprint of Karpenko constructs fields of $u$-invariant $n$ for every $n$
that is neither of the form $2^r - 1$ nor of the form $2^r - 3$ [Karpenko2026]; as of September
2026 it is not yet peer-reviewed.

The problem (`u_invariant_values`) is to determine which integers are $u$-invariants of fields.
The survey [MerkurjevParimala2025, §5.1] records the expectation that every odd integer $\ge 9$
is a $u$-invariant (`u_invariant_values.variants.odd`). Given the results above, the problem is
open exactly for the integers $2^r - 1$ and $2^r - 3$ with $r \ge 4$, the smallest of which are
$13$ and $15$.

*References:*
- [Kaplansky1953] I. Kaplansky, *Quadratic forms*, J. Math. Soc. Japan 5 (1953), 200–207,
  [doi:10.2969/jmsj/00520200](https://doi.org/10.2969/jmsj/00520200).
- [Lam2005] T. Y. Lam, *Introduction to quadratic forms over fields*, Grad. Stud. Math. 67,
  Amer. Math. Soc., 2005, [doi:10.1090/gsm/067](https://doi.org/10.1090/gsm/067).
- [EKM2008] R. Elman, N. Karpenko, A. Merkurjev, *The algebraic and geometric theory of quadratic
  forms*, Amer. Math. Soc. Colloq. Publ. 56, Amer. Math. Soc., 2008,
  [doi:10.1090/coll/056](https://doi.org/10.1090/coll/056).
- [Merkurjev1989] A. S. Merkurjev, *Kaplansky's conjecture in the theory of quadratic forms*
  (Russian), Zap. Nauchn. Sem. LOMI 175 (1989), 75–89; English transl. J. Soviet Math. 57
  (1991), no. 6, 3489–3497, [doi:10.1007/BF01100118](https://doi.org/10.1007/BF01100118).
- [Merkurjev1991] A. S. Merkurjev, *Simple algebras and quadratic forms* (Russian), Izv. Akad.
  Nauk SSSR Ser. Mat. 55 (1991), no. 1, 218–224; English transl. Math. USSR-Izv. 38 (1992),
  no. 1, 215–221,
  [doi:10.1070/IM1992v038n01ABEH002195](https://doi.org/10.1070/IM1992v038n01ABEH002195).
- [Izhboldin2001] O. T. Izhboldin, *Fields of $u$-invariant $9$*, Ann. of Math. (2) 154 (2001),
  no. 3, 529–587, [doi:10.2307/3062141](https://doi.org/10.2307/3062141).
- [Vishik2009] A. Vishik, *Fields of $u$-invariant $2^r + 1$*, pp. 661–685 in Algebra,
  arithmetic, and geometry: in honor of Yu. I. Manin, Vol. II, Progr. Math. 270, Birkhäuser,
  2009, [doi:10.1007/978-0-8176-4747-6_22](https://doi.org/10.1007/978-0-8176-4747-6_22).
- [Karpenko2026] N. A. Karpenko, *Fields of any $u$-invariant but a 2-power minus 1 or 3*,
  preprint, 5 August 2026,
  [author's web page](https://sites.ualberta.ca/~karpenko/publ/u1or3-02.pdf).
- [MerkurjevParimala2025] A. Merkurjev, R. Parimala, *Quadratic forms beyond arithmetic*, Notices
  Amer. Math. Soc. 72 (2025), no. 7, 711–718,
  [doi:10.1090/noti3192](https://doi.org/10.1090/noti3192).
-/

@[expose] public section

namespace KaplanskyUInvariant

open QuadraticForm

/-- `IsUInvariant n` means that some field of characteristic not `2` has $u$-invariant $n$, i.e.
$n$ is the largest dimension of an anisotropic quadratic form over that field.

The field is taken in `Type` (universe $0$), which loses nothing. A quadratic form in $m$
variables is given by finitely many coefficients, so for fixed $n$ the property "characteristic
not $2$ and $u$-invariant $n$" is one first-order sentence in the language of rings: $1 + 1 \ne 0$,
some form in $n$ variables is anisotropic, and every form in $n + 1$ variables is isotropic (then
so is every form in more variables). By the downward Löwenheim–Skolem theorem, a field with this
property in any universe has a countable elementary subfield, which has the same property and is
isomorphic to a field in `Type`. Conversely, `ULift` moves a field in `Type` to any universe. -/
def IsUInvariant (n : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : NeZero (2 : F)), IsGreatest (anisotropicDims F) n

/-- $u(\mathbb{C}) = 1$ [MerkurjevParimala2025, §5.1]: the form $x^2$ is anisotropic, and every
quadratic form in two or more variables over an algebraically closed field is isotropic. -/
@[category test, AMS 11 12]
theorem isGreatest_anisotropicDims_complex : IsGreatest (anisotropicDims ℂ) 1 := by
  refine ⟨one_mem_anisotropicDims ℂ, fun n ⟨Q, hQ, _⟩ ↦ ?_⟩
  by_contra! h
  have hsep : (QuadraticMap.associated (R := ℂ) Q).SeparatingLeft := fun x hx ↦
    hQ x (by simpa [QuadraticMap.associated_eq_self_apply] using hx x)
  obtain ⟨e⟩ := Q.equivalent_weightedSumSquares_of_isAlgClosed hsep
  have hm : 2 ≤ Module.finrank ℂ (Fin n → ℂ) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    exact h
  generalize Module.finrank ℂ (Fin n → ℂ) = m at e hm
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  set v : Fin (k + 2) → ℂ := Fin.cons 1 (Fin.cons Complex.I 0) with hv
  have hv0 : QuadraticMap.weightedSumSquares ℂ (1 : Fin (k + 2) → ℂ) v = 0 := by
    simp [hv, Fin.sum_univ_succ, Complex.I_mul_I]
  have h0 : e.symm v = 0 := hQ _ (by rw [e.symm.map_app, hv0])
  have : v = 0 := e.symm.toLinearEquiv.map_eq_zero_iff.mp h0
  simpa [hv] using congr_fun this 0

/-- $u(\mathbb{R}) = \infty$ [MerkurjevParimala2025, §5.1]: the sum of $n$ squares is anisotropic
for every $n$, so there is no largest dimension of an anisotropic form. -/
@[category test, AMS 11 12]
theorem not_bddAbove_anisotropicDims_real : ¬ BddAbove (anisotropicDims ℝ) := by
  rw [anisotropicDims_eq_univ]
  exact not_bddAbove_univ

/--
**The values of the $u$-invariant**, stated as in [MerkurjevParimala2025, §5.1]: which integers
are $u$-invariants of fields (of characteristic not $2$)? The question goes back to
[Kaplansky1953], who conjectured that only powers of $2$ occur
(`u_invariant_values.variants.kaplansky_conjecture`). Every positive even integer is a
$u$-invariant (`u_invariant_values.variants.even`), $3$, $5$ and $7$ are not
(`u_invariant_values.variants.not_three`, `u_invariant_values.variants.not_five`,
`u_invariant_values.variants.not_seven`), and it is expected that every odd integer $\ge 9$ is
(`u_invariant_values.variants.odd`). Granting the preprint [Karpenko2026]
(`u_invariant_values.variants.karpenko`), the answer is known for every $n$ except $n = 2^r - 1$
and $n = 2^r - 3$ with $r \ge 4$.
-/
@[category research open, AMS 11 12]
theorem u_invariant_values :
    let S : Set ℕ := answer(sorry)
    ∀ n, n ∈ S ↔ IsUInvariant n := by
  sorry

/--
**Kaplansky's conjecture** [Kaplansky1953, p. 202]: the $u$-invariant of a field is a power of
$2$ whenever it is finite. Disproved by Merkurjev, who constructed a field of $u$-invariant $6$
[Merkurjev1989] (`u_invariant_values.variants.even`).
-/
@[category research solved, AMS 11 12]
theorem u_invariant_values.variants.kaplansky_conjecture :
    answer(False) ↔ ∀ n, IsUInvariant n → ∃ k, n = 2 ^ k := by
  sorry

/-- The $u$-invariant is never $3$ [Kaplansky1953, Theorem 2]; see also
[Lam2005, Proposition XI.6.8] and [EKM2008, Corollary 36.4]. -/
@[category research solved, AMS 11 12]
theorem u_invariant_values.variants.not_three : ¬ IsUInvariant 3 := by
  sorry

/-- The $u$-invariant is never $5$ [Lam2005, Proposition XI.6.8], [EKM2008, Corollary 36.4]. -/
@[category research solved, AMS 11 12]
theorem u_invariant_values.variants.not_five : ¬ IsUInvariant 5 := by
  sorry

/-- The $u$-invariant is never $7$ [Lam2005, Proposition XI.6.8], [EKM2008, Corollary 36.4]. -/
@[category research solved, AMS 11 12]
theorem u_invariant_values.variants.not_seven : ¬ IsUInvariant 7 := by
  sorry

open PowerSeries in
/-- Coefficients of a square root of a power series. -/
noncomputable def kuSqrtCoeff {K : Type} [Field K] (u : K⟦X⟧) (c : K) : ℕ → K
  | 0 => c
  | n + 1 => (coeff (n + 1) u - ∑ i : Fin n, kuSqrtCoeff u c (i.1 + 1) * kuSqrtCoeff u c (n - i.1))
      / (2 * c)
decreasing_by
  all_goals (have := i.isLt; omega)

open PowerSeries in
lemma ku_sum_antidiag {K : Type} [Field K] (g : ℕ → K) (n : ℕ) :
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), g p.1 * g p.2 =
      2 * g 0 * g (n + 1) + ∑ i : Fin n, g (i.1 + 1) * g (n - i.1) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    Finset.sum_range_succ', Fin.sum_univ_eq_sum_range (fun i => g (i + 1) * g (n - i))]
  simp only [Nat.sub_self, Nat.sub_zero]
  have : ∀ i ∈ Finset.range n, g (i + 1) * g (n + 1 - (i + 1)) = g (i + 1) * g (n - i) := by
    intro i _; congr 2; omega
  rw [Finset.sum_congr rfl this]
  ring

open PowerSeries in
/-- K2: a power series whose constant coefficient is a nonzero square is a square. -/
lemma ku_sqrt {K : Type} [Field K] [NeZero (2 : K)] (u : K⟦X⟧) (c : K) (hc : c ≠ 0)
    (hu : constantCoeff u = c ^ 2) : ∃ g : K⟦X⟧, g ^ 2 = u ∧ constantCoeff g = c := by
  set g := PowerSeries.mk (kuSqrtCoeff u c)
  have h2 : (2 : K) ≠ 0 := NeZero.ne 2
  refine ⟨g, ?_, ?_⟩
  · ext n
    rw [sq, coeff_mul]
    rcases n with _ | n
    · simp [g, kuSqrtCoeff]
      rw [hu]; ring
    · have := ku_sum_antidiag (kuSqrtCoeff u c) n
      simp only [g, coeff_mk]
      rw [this]
      have hn : kuSqrtCoeff u c (n + 1) = (coeff (n + 1) u - ∑ i : Fin n,
          kuSqrtCoeff u c (i.1 + 1) * kuSqrtCoeff u c (n - i.1)) / (2 * c) := by
        rw [kuSqrtCoeff]
      rw [hn, show kuSqrtCoeff u c 0 = c by rw [kuSqrtCoeff]]
      field_simp
      ring
  · simp [g, kuSqrtCoeff]

open PowerSeries in
/-- The descent step in `K⟦X⟧`. -/
lemma ku_descent {K : Type} [Field K] {m : ℕ} (a : Fin m → K)
    (ha : ∀ t : Fin m → K, ∑ i, a i * t i ^ 2 = 0 → t = 0) (n : ℕ) :
    ∀ x y : Fin m → K⟦X⟧, ∑ i, C (a i) * x i ^ 2 + X * ∑ i, C (a i) * y i ^ 2 = 0 →
      ∀ i, X ^ n ∣ x i ∧ X ^ n ∣ y i := by
  induction n with
  | zero => intro x y _ i; simp
  | succ n ih =>
    intro x y h
    -- constant coefficients of `x` vanish
    have hx0 : ∀ i, constantCoeff (x i) = 0 := by
      have := congrArg constantCoeff h
      simp only [map_add, map_mul, map_sum, constantCoeff_X, zero_mul, add_zero, map_pow,
        constantCoeff_C, map_zero] at this
      exact fun i => by simpa using congrFun (ha (fun i => constantCoeff (x i)) this) i
    choose x' hx' using fun i => X_dvd_iff.mpr (hx0 i)
    have h1 : X * (∑ i, C (a i) * y i ^ 2 + X * ∑ i, C (a i) * x' i ^ 2) = 0 := by
      rw [← h]
      simp only [hx', mul_pow, mul_add, Finset.mul_sum]
      rw [add_comm]
      congr 1
      · apply Finset.sum_congr rfl; intro i _; ring
    have h1' : ∑ i, C (a i) * y i ^ 2 + X * ∑ i, C (a i) * x' i ^ 2 = 0 :=
      (mul_eq_zero.mp h1).resolve_left X_ne_zero
    have hy0 : ∀ i, constantCoeff (y i) = 0 := by
      have := congrArg constantCoeff h1'
      simp only [map_add, map_mul, map_sum, constantCoeff_X, zero_mul, add_zero, map_pow,
        constantCoeff_C, map_zero] at this
      exact fun i => by simpa using congrFun (ha (fun i => constantCoeff (y i)) this) i
    choose y' hy' using fun i => X_dvd_iff.mpr (hy0 i)
    have h2 : X * (∑ i, C (a i) * x' i ^ 2 + X * ∑ i, C (a i) * y' i ^ 2) = 0 := by
      rw [← h1']
      simp only [hy', mul_pow, mul_add, Finset.mul_sum]
      rw [add_comm]
      congr 1
      · apply Finset.sum_congr rfl; intro i _; ring
    have h2' := (mul_eq_zero.mp h2).resolve_left X_ne_zero
    intro i
    obtain ⟨h3, h4⟩ := ih x' y' h2' i
    rw [hx' i, hy' i, pow_succ']
    exact ⟨mul_dvd_mul_left X h3, mul_dvd_mul_left X h4⟩

open PowerSeries in
lemma ku_eq_zero_of_dvd {K : Type} [Field K] (f : K⟦X⟧) (h : ∀ n, X ^ n ∣ f) : f = 0 := by
  ext n
  simpa using (X_pow_dvd_iff.mp (h (n + 1))) n (by omega)

open PowerSeries in
lemma ku_descent_zero {K : Type} [Field K] {m : ℕ} (a : Fin m → K)
    (ha : ∀ t : Fin m → K, ∑ i, a i * t i ^ 2 = 0 → t = 0) (x y : Fin m → K⟦X⟧)
    (h : ∑ i, C (a i) * x i ^ 2 + X * ∑ i, C (a i) * y i ^ 2 = 0) : x = 0 ∧ y = 0 :=
  ⟨funext fun i => ku_eq_zero_of_dvd _ fun n => (ku_descent a ha n x y h i).1,
   funext fun i => ku_eq_zero_of_dvd _ fun n => (ku_descent a ha n x y h i).2⟩

open PowerSeries in
/-- Abbreviation for the embedding `K⟦X⟧ → K((X))`. -/
noncomputable abbrev kuOf (K : Type) [Field K] : K⟦X⟧ →+* LaurentSeries K :=
  HahnSeries.ofPowerSeries ℤ K

open PowerSeries in
lemma ku_single_mul_single {K : Type} [Field K] (a b : ℤ) :
    (HahnSeries.single a (1 : K)) * HahnSeries.single b 1 = HahnSeries.single (a + b) 1 := by
  rw [HahnSeries.single_mul_single, one_mul]

open PowerSeries in
lemma ku_repr {K : Type} [Field K] (f : LaurentSeries K) (d : ℤ) (hd : d ≤ f.order) :
    f = HahnSeries.single d 1 *
      kuOf K (X ^ (f.order - d).toNat * f.powerSeriesPart) := by
  rw [map_mul, HahnSeries.ofPowerSeries_X_pow, LaurentSeries.ofPowerSeries_powerSeriesPart,
    ← mul_assoc, ← mul_assoc, ku_single_mul_single, ku_single_mul_single,
    show d + ((f.order - d).toNat : ℤ) + -f.order = 0 by omega]
  simp

open PowerSeries in
lemma ku_common {K : Type} [Field K] {ι : Type} [Fintype ι] (f : ι → LaurentSeries K) :
    ∃ d : ℤ, ∃ g : ι → K⟦X⟧, ∀ i, f i = HahnSeries.single d 1 * kuOf K (g i) := by
  refine ⟨-∑ j, |(f j).order|, fun i => X ^ ((f i).order - -∑ j, |(f j).order|).toNat *
    (f i).powerSeriesPart, fun i => ku_repr _ _ ?_⟩
  have h1 : |(f i).order| ≤ ∑ j, |(f j).order| :=
    Finset.single_le_sum (f := fun j => |(f j).order|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have h2 := neg_abs_le (f i).order
  linarith

open PowerSeries in
/-- K3: the lower-bound form `⟨a⟩ ⊥ X⟨a⟩` is anisotropic over `K((X))`. -/
lemma ku_lower {K : Type} [Field K] {m : ℕ} (a : Fin m → K)
    (ha : ∀ t : Fin m → K, ∑ i, a i * t i ^ 2 = 0 → t = 0) (x y : Fin m → LaurentSeries K)
    (h : ∑ i, kuOf K (C (a i)) * x i ^ 2 + kuOf K X * ∑ i, kuOf K (C (a i)) * y i ^ 2 = 0) :
    x = 0 ∧ y = 0 := by
  obtain ⟨d, g, hg⟩ := ku_common (Sum.elim x y)
  have hx : ∀ i, x i = HahnSeries.single d 1 * kuOf K (g (Sum.inl i)) := fun i => hg (Sum.inl i)
  have hy : ∀ i, y i = HahnSeries.single d 1 * kuOf K (g (Sum.inr i)) := fun i => hg (Sum.inr i)
  have key : HahnSeries.single (d + d) (1 : K) * kuOf K (∑ i, C (a i) * g (Sum.inl i) ^ 2 +
      X * ∑ i, C (a i) * g (Sum.inr i) ^ 2) = 0 := by
    rw [← h]
    simp only [hx, hy, map_add, map_mul, map_sum, map_pow, mul_pow, sq, ← ku_single_mul_single]
    simp only [mul_add, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl; intro i _; ring
    · apply Finset.sum_congr rfl; intro i _; ring
  have hs : HahnSeries.single (d + d) (1 : K) ≠ 0 := by simp
  have h0 := (mul_eq_zero.mp key).resolve_left hs
  rw [map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective] at h0
  obtain ⟨h1, h2⟩ := ku_descent_zero a ha _ _ h0
  constructor
  · funext i; rw [hx i, show g (Sum.inl i) = 0 from congrFun h1 i]; simp
  · funext i; rw [hy i, show g (Sum.inr i) = 0 from congrFun h2 i]; simp

open PowerSeries in
lemma ku_nondeg {F : Type} [Field F] (h2 : (2 : F) ≠ 0) {n : ℕ}
    (Q : QuadraticForm F (Fin n → F)) (hQ : Q.Anisotropic) : Q.Nondegenerate := by
  have hker : LinearMap.ker Q.polarBilin = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have h1 : QuadraticMap.polar Q x x = 0 := by
      rw [← QuadraticMap.polarBilin_apply_apply, LinearMap.mem_ker.mp hx]; rfl
    rw [QuadraticMap.polar_self, nsmul_eq_mul] at h1
    push_cast at h1
    exact hQ x ((mul_eq_zero.mp h1).resolve_left (by exact_mod_cast h2))
  refine ⟨?_, ?_⟩
  · rw [Submodule.eq_bot_iff]
    intro x hx
    exact hQ x hx.1
  · rw [hker, rank_bot]; exact zero_le_one

open PowerSeries in
lemma ku_aniso_of_equiv {F V W : Type} [Field F] [AddCommGroup V] [Module F V] [AddCommGroup W]
    [Module F W] {Q₁ : QuadraticForm F V} {Q₂ : QuadraticForm F W} (h : Q₁.Equivalent Q₂)
    (h₂ : Q₂.Anisotropic) : Q₁.Anisotropic := by
  obtain ⟨f⟩ := h
  intro x hx
  have : Q₂ (f x) = 0 := by rw [f.map_app]; exact hx
  have := h₂ _ this
  exact f.toLinearEquiv.map_eq_zero_iff.mp this

open PowerSeries in
lemma ku_wss_aniso_iff {F : Type} [Field F] {n : ℕ} (w : Fin n → F) :
    (QuadraticMap.weightedSumSquares F w).Anisotropic ↔
      ∀ t : Fin n → F, ∑ i, w i * t i ^ 2 = 0 → t = 0 := by
  unfold QuadraticMap.Anisotropic
  simp only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul, sq]

open PowerSeries in
lemma ku_two_ne_zero (K : Type) [Field K] [NeZero (2 : K)] : (2 : LaurentSeries K) ≠ 0 := by
  intro h
  have h' : kuOf K 2 = kuOf K 0 := by rw [map_ofNat, h, map_zero]
  have := congrArg constantCoeff (HahnSeries.ofPowerSeries_injective h')
  rw [map_ofNat, map_zero] at this
  exact NeZero.ne (2 : K) this

open PowerSeries in
/-- K6a: if `K` has an anisotropic form of dimension `m`, `K((X))` has one of dimension `2m`. -/
lemma ku_mem_double {K : Type} [Field K] [NeZero (2 : K)] {m : ℕ}
    (hm : m ∈ QuadraticForm.anisotropicDims K) :
    2 * m ∈ QuadraticForm.anisotropicDims (LaurentSeries K) := by
  obtain ⟨Q, hQa, -⟩ := hm
  haveI : Invertible (2 : K) := invertibleOfNonzero (NeZero.ne 2)
  obtain ⟨w, hw⟩ := QuadraticForm.equivalent_weightedSumSquares Q
  have haw : (QuadraticMap.weightedSumSquares K w).Anisotropic := by
    obtain ⟨f⟩ := hw
    exact ku_aniso_of_equiv ⟨f.symm⟩ hQa
  generalize hr : Module.finrank K (Fin m → K) = r at w haw
  have hrm : r = m := by rw [← hr, Module.finrank_fin_fun]
  subst hrm
  rw [ku_wss_aniso_iff] at haw
  set b : Fin (r + r) → LaurentSeries K :=
    Fin.append (fun i => kuOf K (C (w i))) (fun i => kuOf K X * kuOf K (C (w i)))
  have hb : (QuadraticMap.weightedSumSquares (LaurentSeries K) b).Anisotropic := by
    rw [ku_wss_aniso_iff]
    intro t ht
    rw [Fin.sum_univ_add] at ht
    simp only [b, Fin.append_left, Fin.append_right] at ht
    have ht' : ∑ i, kuOf K (C (w i)) * (t (Fin.castAdd r i)) ^ 2 +
        kuOf K X * ∑ i, kuOf K (C (w i)) * (t (Fin.natAdd r i)) ^ 2 = 0 := by
      rw [← ht, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl; intro i _; ring
    obtain ⟨h1, h2⟩ := ku_lower w haw _ _ ht'
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · exact congrFun h1 i
    · exact congrFun h2 i
  rw [two_mul]
  exact ⟨_, hb, ku_nondeg (ku_two_ne_zero K) _ hb⟩

open PowerSeries in
/-- K5a: lifting an isotropic residue vector. -/
lemma ku_lift {K : Type} [Field K] [NeZero (2 : K)] {J : Type} [Fintype J] [DecidableEq J]
    (u : J → K⟦X⟧) (hu : ∀ j, constantCoeff (u j) ≠ 0) (t : J → K) (ht : t ≠ 0)
    (hsum : ∑ j, constantCoeff (u j) * t j ^ 2 = 0) :
    ∃ z : J → K⟦X⟧, z ≠ 0 ∧ ∑ j, u j * z j ^ 2 = 0 := by
  obtain ⟨j0, hj0⟩ := Function.ne_iff.mp ht
  simp only [Pi.zero_apply] at hj0
  set S := ∑ j ∈ Finset.univ.erase j0, u j * C (t j) ^ 2
  set r := -S * (u j0)⁻¹
  have hS : constantCoeff S = -(constantCoeff (u j0) * t j0 ^ 2) := by
    have := Finset.add_sum_erase Finset.univ (fun j => constantCoeff (u j) * t j ^ 2)
      (Finset.mem_univ j0)
    rw [hsum] at this
    simp only [S, map_sum, map_mul, map_pow, constantCoeff_C]
    linear_combination this
  have hr : constantCoeff r = t j0 ^ 2 := by
    simp only [r, map_mul, map_neg, constantCoeff_inv, hS]
    field_simp [hu j0]
  obtain ⟨g, hg, hg0⟩ := ku_sqrt r (t j0) hj0 hr
  refine ⟨Function.update (fun j => C (t j)) j0 g, ?_, ?_⟩
  · intro h
    have := congrFun h j0
    simp only [Function.update_self, Pi.zero_apply] at this
    rw [this, map_zero] at hg0
    exact hj0 hg0.symm
  · rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j0)]
    simp only [Function.update_self]
    have : ∑ x ∈ Finset.univ.erase j0, u x * Function.update (fun j => C (t j)) j0 g x ^ 2 = S := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    rw [this, hg]
    simp only [r]
    have hinv := PowerSeries.mul_inv_cancel (u j0) (hu j0)
    linear_combination (-S) * hinv

open PowerSeries in
/-- K5b: a diagonal form over `K` in more than `u(K)` variables is isotropic. -/
lemma ku_residue {K : Type} [Field K] [NeZero (2 : K)] {m : ℕ}
    (hub : ∀ n ∈ QuadraticForm.anisotropicDims K, n ≤ m) {J : Type} [Fintype J]
    (c : J → K) (hJ : m < Fintype.card J) :
    ∃ t : J → K, t ≠ 0 ∧ ∑ j, c j * t j ^ 2 = 0 := by
  by_contra hno
  push Not at hno
  set e := Fintype.equivFin J
  have han : (QuadraticMap.weightedSumSquares K (c ∘ e.symm)).Anisotropic := by
    rw [ku_wss_aniso_iff]
    intro s hs
    by_contra hs0
    have h1 : (fun j => s (e j)) ≠ 0 := by
      intro h
      apply hs0
      funext k
      have := congrFun h (e.symm k)
      simpa using this
    apply hno _ h1
    rw [← hs, ← Equiv.sum_comp e]
    simp
  have hmem : Fintype.card J ∈ QuadraticForm.anisotropicDims K :=
    ⟨_, han, ku_nondeg (NeZero.ne 2) _ han⟩
  exact absurd (hub _ hmem) (by omega)

open PowerSeries in
lemma ku_normal {K : Type} [Field K] (f : LaurentSeries K) (hf : f ≠ 0) :
    f = HahnSeries.single f.order 1 * kuOf K f.powerSeriesPart ∧
      constantCoeff f.powerSeriesPart ≠ 0 := by
  constructor
  · have := ku_repr f f.order le_rfl
    simpa using this
  · rw [← coeff_zero_eq_constantCoeff_apply, LaurentSeries.powerSeriesPart_coeff]
    simpa using (HahnSeries.coeff_order_eq_zero (x := f)).not.mpr hf

open PowerSeries in
/-- K5c: a diagonal form over `K((X))` in more than `2 u(K)` variables is isotropic. -/
lemma ku_upper {K : Type} [Field K] [NeZero (2 : K)] {m : ℕ}
    (hub : ∀ n ∈ QuadraticForm.anisotropicDims K, n ≤ m) {n : ℕ} (hn : 2 * m < n)
    (w : Fin n → LaurentSeries K) :
    ∃ v : Fin n → LaurentSeries K, v ≠ 0 ∧ ∑ i, w i * v i ^ 2 = 0 := by
  classical
  by_cases hz : ∃ i, w i = 0
  · obtain ⟨i, hi⟩ := hz
    refine ⟨Pi.single i (1 : LaurentSeries K), fun h => by simpa using congrFun h i, ?_⟩
    rw [Finset.sum_eq_single i]
    · simp [hi]
    · intro b _ hb; simp [Pi.single_eq_of_ne hb]
    · simp
  push Not at hz
  set o : Fin n → ℤ := fun i => (w i).order
  set u : Fin n → K⟦X⟧ := fun i => (w i).powerSeriesPart
  have hw : ∀ i, w i = HahnSeries.single (o i) 1 * kuOf K (u i) := fun i => (ku_normal _ (hz i)).1
  have hu0 : ∀ i, constantCoeff (u i) ≠ 0 := fun i => (ku_normal _ (hz i)).2
  set P : ℤ → Finset (Fin n) := fun e => Finset.univ.filter (fun i => o i % 2 = e)
  obtain ⟨e, hPe⟩ : ∃ e, m < (P e).card := by
    by_contra hc
    push Not at hc
    have hsub : (Finset.univ : Finset (Fin n)) ⊆ P 0 ∪ P 1 := by
      intro i _
      rcases Int.emod_two_eq (o i) with h | h
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    simp at this
    have := hc 0; have := hc 1
    omega
  set J := {i // i ∈ P e}
  have hJ : m < Fintype.card J := by simpa [J] using hPe
  obtain ⟨t, ht, hts⟩ := ku_residue hub (fun j : J => constantCoeff (u j.1)) hJ
  obtain ⟨z, hz0, hzs⟩ := ku_lift (fun j : J => u j.1) (fun j => hu0 j.1) t ht hts
  set v : Fin n → LaurentSeries K := fun i =>
    if h : i ∈ P e then HahnSeries.single (-(o i / 2)) 1 * kuOf K (z ⟨i, h⟩) else 0
  have hterm : ∀ j : J, w j.1 * v j.1 ^ 2 =
      HahnSeries.single e 1 * kuOf K (u j.1 * z j ^ 2) := by
    intro j
    have hje : o j.1 % 2 = e := (Finset.mem_filter.mp j.2).2
    simp only [v, dif_pos j.2, hw, map_mul, map_pow, mul_pow]
    have hsq : (HahnSeries.single (-(o j.1 / 2)) (1 : K)) ^ 2 =
        HahnSeries.single (-(o j.1 / 2) + -(o j.1 / 2)) 1 := by
      rw [sq, ku_single_mul_single]
    have hoe : o j.1 + (-(o j.1 / 2) + -(o j.1 / 2)) = e := by
      have := Int.emod_add_mul_ediv (o j.1) 2
      omega
    rw [hsq]
    calc HahnSeries.single (o j.1) 1 * kuOf K (u j.1) *
          (HahnSeries.single (-(o j.1 / 2) + -(o j.1 / 2)) 1 * kuOf K (z ⟨j.1, j.2⟩) ^ 2)
        = (HahnSeries.single (o j.1) 1 * HahnSeries.single (-(o j.1 / 2) + -(o j.1 / 2)) 1) *
          (kuOf K (u j.1) * kuOf K (z j) ^ 2) := by ring
      _ = _ := by rw [ku_single_mul_single, hoe]
  refine ⟨v, ?_, ?_⟩
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp hz0
    intro hv
    have := congrFun hv j.1
    simp only [v, dif_pos j.2, Pi.zero_apply] at this
    rcases mul_eq_zero.mp this with h | h
    · simp at h
    · exact hj ((map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective).mp h)
  · have hout : ∀ i ∈ (Finset.univ : Finset (Fin n)), i ∉ P e → w i * v i ^ 2 = 0 := by
      intro i _ hi; simp [v, dif_neg hi]
    rw [← Finset.sum_subset (Finset.subset_univ (P e)) hout, ← Finset.sum_coe_sort (P e)]
    rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.mul_sum, ← map_sum, hzs]
    simp

open PowerSeries in
/-- K6: `u(K((X))) = 2 u(K)`. -/
lemma ku_step {K : Type} [Field K] [NeZero (2 : K)] {m : ℕ}
    (h : IsGreatest (QuadraticForm.anisotropicDims K) m) :
    IsGreatest (QuadraticForm.anisotropicDims (LaurentSeries K)) (2 * m) := by
  refine ⟨ku_mem_double h.1, ?_⟩
  rintro n ⟨Q, hQ, -⟩
  by_contra hlt
  push Not at hlt
  have : Invertible (2 : LaurentSeries K) := invertibleOfNonzero (ku_two_ne_zero K)
  obtain ⟨w, hw⟩ := QuadraticForm.equivalent_weightedSumSquares Q
  have haw : (QuadraticMap.weightedSumSquares (LaurentSeries K) w).Anisotropic :=
    ku_aniso_of_equiv hw.symm hQ
  generalize hr : Module.finrank (LaurentSeries K) (Fin n → LaurentSeries K) = r at w haw
  have hrn : r = n := by rw [← hr, Module.finrank_fin_fun]
  subst hrn
  rw [ku_wss_aniso_iff] at haw
  obtain ⟨v, hv, hvs⟩ := ku_upper h.2 hlt w
  exact hv (haw v hvs)

/--
Every power of $2$ is a $u$-invariant [Kaplansky1953, p. 202]: Theorem 3 of [Kaplansky1953]
gives $u(F((t))) = 2u(F)$, so $u(\mathbb{C}((t_1)) \cdots ((t_k))) = 2^k$; see also
[EKM2008, §38].
-/
@[category research solved, AMS 11 12]
theorem u_invariant_values.variants.two_pow (k : ℕ) : IsUInvariant (2 ^ k) := by
  induction k with
  | zero => exact ⟨ℂ, inferInstance, ⟨two_ne_zero⟩, by simpa using isGreatest_anisotropicDims_complex⟩
  | succ k ih =>
    obtain ⟨F, _, _, hG⟩ := ih
    exact ⟨LaurentSeries F, inferInstance, ⟨ku_two_ne_zero F⟩, by
      rw [pow_succ, mul_comm]; exact ku_step hG⟩

/--
**Merkurjev's theorem** [Merkurjev1991], see also [EKM2008, Theorem 38.4]: every positive even
integer is a $u$-invariant. The case $6$, the first counterexample to Kaplansky's conjecture, is
[Merkurjev1989].
-/
@[category research solved, AMS 11 12]
theorem u_invariant_values.variants.even (n : ℕ) (hn : Even n) (hn₀ : n ≠ 0) :
    IsUInvariant n := by
  sorry

/-- **Izhboldin's theorem** [Izhboldin2001]: there is a field of $u$-invariant $9$,
the first example of an odd $u$-invariant greater than $1$. -/
@[category research solved, AMS 11 12]
theorem u_invariant_values.variants.nine : IsUInvariant 9 := by
  sorry

/-- **Vishik's theorem** [Vishik2009, Corollary 5.2]: for every $r \ge 3$ there is a field of
$u$-invariant $2^r + 1$. -/
@[category research solved, AMS 11 12]
theorem u_invariant_values.variants.two_pow_add_one (r : ℕ) (hr : 3 ≤ r) :
    IsUInvariant (2 ^ r + 1) := by
  sorry

/--
**Karpenko's theorem** [Karpenko2026, Theorem 1.1]: if neither $n + 1$ nor $n + 3$ is a power
of $2$, then there is a field of $u$-invariant $n$. This covers every positive integer except
$1$, $3$, $5$, $7$ and the integers $2^r - 1$, $2^r - 3$ with $r \ge 4$. As of September 2026
the result is a preprint and not yet peer-reviewed.
-/
@[category research solved, AMS 11 12]
theorem u_invariant_values.variants.karpenko (n : ℕ) (h₁ : ∀ r, 2 ^ r ≠ n + 1)
    (h₃ : ∀ r, 2 ^ r ≠ n + 3) : IsUInvariant n := by
  sorry

/--
The special case $n = 11$ of `u_invariant_values.variants.karpenko` (neither $12$ nor $14$ is a
power of $2$), the first odd value not of the form $2^r + 1$ shown to be a $u$-invariant; it was
announced in the preprint *Fields of $u$-invariant 11* (21 April 2026) that [Karpenko2026]
absorbs.
-/
@[category research solved, AMS 11 12]
theorem u_invariant_values.variants.eleven : IsUInvariant 11 := by
  refine u_invariant_values.variants.karpenko 11 (fun r h ↦ ?_) (fun r h ↦ ?_) <;>
  · rcases Nat.lt_or_ge r 4 with hr | hr
    · interval_cases r <;> simp_all
    · have := Nat.pow_le_pow_right two_pos hr
      omega

/--
The expectation recorded in [MerkurjevParimala2025, §5.1]: every odd integer $\ge 9$ is a
$u$-invariant. By `u_invariant_values.variants.karpenko` this is open exactly for the integers
$2^r - 1$ and $2^r - 3$ with $r \ge 4$.
-/
@[category research open, AMS 11 12]
theorem u_invariant_values.variants.odd :
    answer(sorry) ↔ ∀ n, Odd n → 9 ≤ n → IsUInvariant n := by
  sorry

/-- The smallest open case of the form $2^r - 3$: is there a field of $u$-invariant $13$? -/
@[category research open, AMS 11 12]
theorem u_invariant_values.variants.thirteen : answer(sorry) ↔ IsUInvariant 13 := by
  sorry

/-- The smallest open case of the form $2^r - 1$: is there a field of $u$-invariant $15$? -/
@[category research open, AMS 11 12]
theorem u_invariant_values.variants.fifteen : answer(sorry) ↔ IsUInvariant 15 := by
  sorry

end KaplanskyUInvariant
