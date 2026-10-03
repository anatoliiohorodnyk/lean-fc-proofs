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
# Erdős Problem 30

*References:*
- [erdosproblems.com/30](https://www.erdosproblems.com/30)
- [ErTu41] Erdős, P. and Turán, P., *On a problem of Sidon in additive number theory, and on
  some related problems*. J. London Math. Soc. 16 (1941), 212-215.
- [Li69] Lindström, B., *An inequality for $B_2$-sequences*. J. Combinatorial Theory 6 (1969),
  211-212.
- [Si38] Singer, J., *A theorem in finite projective geometry and some applications to number
  theory*. Trans. Amer. Math. Soc. 43 (1938), 377-385.
- [BFR23] Balogh, J., Füredi, Z. and Roy, S., *An upper bound on the size of Sidon sets*.
  Amer. Math. Monthly 130 (2023), 437-445.
- [OB22] O'Bryant, K., *On the size of finite Sidon sets*.
  [arXiv:2207.07800](https://arxiv.org/abs/2207.07800) (2022).
- [CHO25] Carter, D., Hunter, Z. and O'Bryant, K., *On the diameter of finite Sidon sets*.
  Acta Math. Hungar. 175 (2025), 108-126.

See also [Ben Green's Open Problem 31](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf)
(formalised in `FormalConjectures/GreensOpenProblems/31.lean`).
-/

@[expose] public section

namespace Erdos30

/--
Let $h(N)$ be the maximum size of a Sidon set in $\{1, \dots, N\}$.
-/
noncomputable abbrev h (N : ℕ) : ℕ := Finset.maxSidonSubsetCard (Finset.Icc 1 N)


open Filter
open scoped Asymptotics

/--
Is it true that, for every $\varepsilon > 0$, $h(N) = \sqrt N + O_{\varepsilon}(N^\varepsilon)$
-/
@[category research open, AMS 11]
theorem erdos_30 : answer(sorry) ↔
    ∀ᵉ (ε > 0), (fun N => h N - (N : Real).sqrt) =O[atTop] fun N => (N : ℝ)^(ε : ℝ) := by
  sorry

/--
A stronger conjecture: is it true that $h(N) = \sqrt N + O(1)$?
Erdős thought this was perhaps too optimistic.
-/
@[category research open, AMS 11]
theorem erdos_30.variants.O_one : answer(sorry) ↔
    (fun N => h N - (N : ℝ).sqrt) =O[atTop] fun _ => (1 : ℝ) := by
  sorry

/--
Erdős and Turán [ErTu41] proved $h(N) \le \sqrt N + O(N^{1/4})$.
-/
@[category research solved, AMS 11]
theorem erdos_30.variants.erdos_turan :
    (fun N => h N - (N : ℝ).sqrt) =O[atTop] fun N => (N : ℝ) ^ (4⁻¹ : ℝ) := by
  sorry

lemma e30_tele (f : ℕ → ℤ) (t m : ℕ) :
    ∑ i ∈ Finset.range m, (f (i + t) - f i) =
      ∑ i ∈ Finset.range t, f (m + i) - ∑ i ∈ Finset.range t, f i := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : ∑ i ∈ Finset.range t, f (m + 1 + i) =
        ∑ i ∈ Finset.range t, f (m + i) + f (m + t) - f m := by
      have := Finset.sum_range_succ (fun i => f (m + i)) t
      have h2 := Finset.sum_range_succ' (fun i => f (m + i)) t
      simp only [add_zero] at h2
      have h3 : ∑ i ∈ Finset.range t, f (m + (i + 1)) = ∑ i ∈ Finset.range t, f (m + 1 + i) :=
        Finset.sum_congr rfl (fun i _ => by ring_nf)
      linarith
    rw [h1, add_comm m t]; ring

lemma e30_distinct (S : Finset ℕ) (hS : ∀ x ∈ S, 1 ≤ x) : S.card * (S.card + 1) ≤ 2 * ∑ x ∈ S, x := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert b s hb ih =>
    have hbs : b ∉ s := fun h => lt_irrefl _ (hb b h)
    rw [Finset.card_insert_of_notMem hbs, Finset.sum_insert hbs]
    have ih' := ih (fun x hx => hS x (Finset.mem_insert_of_mem hx))
    have hsub : s ⊆ Finset.Icc 1 (b - 1) := by
      intro x hx
      have := hS x (Finset.mem_insert_of_mem hx)
      have := hb x hx
      simp only [Finset.mem_Icc]; omega
    have hcard : s.card ≤ b - 1 := by
      have := Finset.card_le_card hsub; simpa using this
    have hb1 := hS b (Finset.mem_insert_self _ _)
    have hc : s.card + 1 ≤ b := by omega
    nlinarith [ih', hc]

lemma e30_gauss (u : ℕ) : 2 * ∑ t ∈ Finset.range u, (t + 1) = u * (u + 1) := by
  induction u with
  | zero => simp
  | succ u ih => rw [Finset.sum_range_succ]; nlinarith

lemma e30_count (u k : ℕ) (hu : u ≤ k) :
    ∑ t ∈ Finset.range u, (k - (t + 1)) + ∑ t ∈ Finset.range u, (t + 1) = u * k := by
  induction u with
  | zero => simp
  | succ u ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have := ih (by omega)
    have : k - (u + 1) + (u + 1) = k := by omega
    nlinarith

lemma e30_core (N k u : ℕ) (a : ℕ → ℕ) (hmono : ∀ i j, i < j → j < k → a i < a j)
    (hpos : ∀ i < k, 1 ≤ a i) (hN : ∀ i < k, a i ≤ N)
    (hsid : ∀ i j l m, i < k → j < k → l < k → m < k → a i + a j = a l + a m →
      (i = l ∧ j = m) ∨ (i = m ∧ j = l)) (hu : u ≤ k) :
    let M := ∑ t ∈ Finset.range u, (k - (t + 1))
    M * (M + 1) ≤ N * (u * (u + 1)) := by
  intro M
  let D := (Finset.range u).sigma (fun t => Finset.range (k - (t + 1)))
  let g : (Σ _ : ℕ, ℕ) → ℕ := fun x => a (x.2 + (x.1 + 1)) - a x.2
  have hD : ∀ x ∈ D, x.1 < u ∧ x.2 + (x.1 + 1) < k := by
    intro x hx
    simp only [D, Finset.mem_sigma, Finset.mem_range] at hx
    omega
  have hinj : Set.InjOn g D := by
    intro x hx y hy hxy
    obtain ⟨hx1, hx2⟩ := hD x hx
    obtain ⟨hy1, hy2⟩ := hD y hy
    simp only [g] at hxy
    have h1 := hmono x.2 (x.2 + (x.1 + 1)) (by omega) hx2
    have h2 := hmono y.2 (y.2 + (y.1 + 1)) (by omega) hy2
    have hs : a (x.2 + (x.1 + 1)) + a y.2 = a (y.2 + (y.1 + 1)) + a x.2 := by omega
    rcases hsid _ _ _ _ hx2 (by omega) hy2 (by omega) hs with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · obtain ⟨x1, x2⟩ := x; obtain ⟨y1, y2⟩ := y
      simp only at e1 e2 ⊢
      subst e2
      have : x1 = y1 := by omega
      subst this; rfl
    · omega
  have hcardD : D.card = M := by simp [D, M, Finset.card_sigma]
  have himg : (D.image g).card = M := by rw [Finset.card_image_of_injOn hinj, hcardD]
  have hpos' : ∀ x ∈ D.image g, 1 ≤ x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hy1, hy2⟩ := hD y hy
    have := hmono y.2 (y.2 + (y.1 + 1)) (by omega) hy2
    simp only [g]; omega
  have hdist := e30_distinct (D.image g) hpos'
  rw [himg, Finset.sum_image hinj] at hdist
  -- bound the sum
  have hsum : ∑ x ∈ D, g x ≤ ∑ t ∈ Finset.range u, (t + 1) * N := by
    rw [Finset.sum_sigma]
    apply Finset.sum_le_sum
    intro t ht
    rw [Finset.mem_range] at ht
    have hz : ((∑ i ∈ Finset.range (k - (t + 1)), (a (i + (t + 1)) - a i) : ℕ) : ℤ) ≤
        (((t + 1) * N : ℕ) : ℤ) := by
      rw [Nat.cast_sum]
      have hcast : ∑ i ∈ Finset.range (k - (t + 1)), ((a (i + (t + 1)) - a i : ℕ) : ℤ) =
          ∑ i ∈ Finset.range (k - (t + 1)), ((a (i + (t + 1)) : ℤ) - (a i : ℤ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_range] at hi
        exact Nat.cast_sub (hmono i (i + (t + 1)) (by omega) (by omega)).le
      rw [hcast]
      rw [e30_tele (fun i => (a i : ℤ)) (t + 1) (k - (t + 1))]
      have h1 : ∑ i ∈ Finset.range (t + 1), ((a (k - (t + 1) + i) : ℕ) : ℤ) ≤
          ∑ i ∈ Finset.range (t + 1), (N : ℤ) :=
        Finset.sum_le_sum (fun i hi => by
          rw [Finset.mem_range] at hi; exact_mod_cast hN _ (by omega))
      have h2 : 0 ≤ ∑ i ∈ Finset.range (t + 1), ((a i : ℕ) : ℤ) :=
        Finset.sum_nonneg (fun i _ => by positivity)
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
      push_cast at h1 ⊢
      linarith
    exact_mod_cast hz
  have hg := e30_gauss u
  have : ∑ t ∈ Finset.range u, (t + 1) * N = (∑ t ∈ Finset.range u, (t + 1)) * N :=
    (Finset.sum_mul _ _ _).symm
  nlinarith

lemma e30_card (N : ℕ) (B : Finset ℕ) (hB : B ⊆ Finset.Icc 1 N) (hS : IsSidon (B : Set ℕ)) :
    (B.card : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 := by
  set k := B.card with hk
  set q : ℝ := (N : ℝ) ^ (4⁻¹ : ℝ) with hqdef
  set s : ℝ := (N : ℝ).sqrt with hsdef
  have hq0 : 0 ≤ q := by positivity
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hq2 : q ^ 2 = s := by
    rw [hqdef, hsdef, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), Real.sqrt_eq_rpow]
    norm_num
  have hs2 : s ^ 2 = N := Real.sq_sqrt (by positivity)
  rcases Nat.eq_zero_or_pos N with hN0 | hN0
  · have : B = ∅ := by
      apply Finset.subset_empty.mp
      intro x hx; have := hB hx; simp [hN0] at this
    rw [hk, this]; simp; positivity
  have hqpos : 0 < q := Real.rpow_pos_of_pos (by exact_mod_cast hN0) _
  set u := ⌈q⌉₊ with hudef
  have hu1 : q ≤ u := Nat.le_ceil q
  have hu2 : (u : ℝ) < q + 1 := Nat.ceil_lt_add_one hq0
  rcases Nat.lt_or_ge k u with hlt | hge
  · have : (k : ℝ) + 1 ≤ u := by exact_mod_cast hlt
    linarith
  · -- the sorted enumeration
    let e := B.orderEmbOfFin rfl
    let a : ℕ → ℕ := fun i => if hi : i < k then e ⟨i, hi⟩ else 0
    have ha : ∀ i (hi : i < k), a i = e ⟨i, hi⟩ := fun i hi => by simp [a, hi]
    have hmemB : ∀ i (hi : i < k), a i ∈ B := fun i hi => by
      rw [ha i hi]; exact Finset.orderEmbOfFin_mem B rfl _
    have hmono : ∀ i j, i < j → j < k → a i < a j := by
      intro i j hij hj
      rw [ha i (by omega), ha j hj]
      exact e.strictMono (by simp [Fin.lt_def, hij])
    have hinj : ∀ i j, i < k → j < k → a i = a j → i = j := by
      intro i j hi hj hij
      rcases lt_trichotomy i j with h | h | h
      · exact absurd hij (hmono i j h hj).ne
      · exact h
      · exact absurd hij (hmono j i h hi).ne'
    have hpos : ∀ i < k, 1 ≤ a i := fun i hi => (Finset.mem_Icc.mp (hB (hmemB i hi))).1
    have hN : ∀ i < k, a i ≤ N := fun i hi => (Finset.mem_Icc.mp (hB (hmemB i hi))).2
    have hsid : ∀ i j l m, i < k → j < k → l < k → m < k → a i + a j = a l + a m →
        (i = l ∧ j = m) ∨ (i = m ∧ j = l) := by
      intro i j l m hi hj hl hm hsum
      rcases hS (a i) (hmemB i hi) (a l) (hmemB l hl) (a j) (hmemB j hj) (a m) (hmemB m hm) hsum
        with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨hinj _ _ hi hl h1, hinj _ _ hj hm h2⟩
      · exact Or.inr ⟨hinj _ _ hi hm h1, hinj _ _ hj hl h2⟩
    have hcore := e30_core N k u a hmono hpos hN hsid hge
    simp only at hcore
    set M := ∑ t ∈ Finset.range u, (k - (t + 1)) with hM
    have hcount := e30_count u k hge
    have hgauss := e30_gauss u
    rw [← hM] at hcount
    set T := ∑ t ∈ Finset.range u, (t + 1)
    have hcoreR : (M : ℝ) * (M + 1) ≤ N * (u * (u + 1)) := by exact_mod_cast hcore
    have hcountR : (M : ℝ) + T = u * k := by exact_mod_cast hcount
    have hgaussR : 2 * (T : ℝ) = u * (u + 1) := by exact_mod_cast hgauss
    have hupos : (0 : ℝ) < u := lt_of_lt_of_le hqpos hu1
    have hM0 : (0 : ℝ) ≤ M := by positivity
    have hMle : (M : ℝ) ≤ s * (u + 1 / 2) := by
      by_contra hcon
      push Not at hcon
      have h1 : (s * (u + 1 / 2)) ^ 2 < (M : ℝ) ^ 2 := by
        have : 0 ≤ s * (u + 1 / 2) := by positivity
        nlinarith
      have h2 : (s * (u + 1 / 2)) ^ 2 = N * (u * (u + 1)) + N / 4 := by
        rw [mul_pow, hs2]; ring
      have h3 : (0 : ℝ) ≤ N := by positivity
      nlinarith
    have hsq : s ≤ u * q := by rw [← hq2]; nlinarith
    have hfin : (u : ℝ) * k ≤ u * (s + q + 1) := by nlinarith
    exact le_of_mul_le_mul_left hfin hupos

/--
The proofs of Erdős–Turán [ErTu41] and Lindström [Li69] in fact give, for all $N$,
$h(N) \le N^{1/2} + N^{1/4} + 1$.
-/
@[category research solved, AMS 11]
theorem erdos_30.variants.lindstrom (N : ℕ) :
    (h N : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 := by
  obtain ⟨B, hBmem, hBeq⟩ := Finset.exists_mem_eq_sup
    ((Finset.Icc 1 N).powerset.filter fun B : Finset ℕ => IsSidon (B : Set ℕ))
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _, by simp [IsSidon]⟩⟩ Finset.card
  rw [Finset.mem_filter, Finset.mem_powerset] at hBmem
  show ((Finset.maxSidonSubsetCard (Finset.Icc 1 N) : ℕ) : ℝ) ≤ _
  unfold Finset.maxSidonSubsetCard
  rw [hBeq]
  exact e30_card N B hBmem.1 hBmem.2

/--
Balogh, Füredi and Roy [BFR23] proved $h(N) \le N^{1/2} + 0.998 N^{1/4}$ for all sufficiently
large $N$.
-/
@[category research solved, AMS 11]
theorem erdos_30.variants.balogh_furedi_roy :
    ∀ᶠ N in atTop, (h N : ℝ) ≤ (N : ℝ).sqrt + (0.998 : ℝ) * (N : ℝ) ^ (4⁻¹ : ℝ) := by
  sorry

/--
O'Bryant [OB22] proved $h(N) \le N^{1/2} + 0.99703 N^{1/4}$ for all sufficiently large $N$.
-/
@[category research solved, AMS 11]
theorem erdos_30.variants.obryant :
    ∀ᶠ N in atTop, (h N : ℝ) ≤ (N : ℝ).sqrt + (0.99703 : ℝ) * (N : ℝ) ^ (4⁻¹ : ℝ) := by
  sorry

/--
Carter, Hunter and O'Bryant [CHO25] proved $h(N) \le N^{1/2} + 0.98183 N^{1/4} + O(1)$.
This is the current record upper bound.
-/
@[category research solved, AMS 11]
theorem erdos_30.variants.carter_hunter_obryant :
    ∃ C : ℝ, ∀ᶠ N in atTop,
      (h N : ℝ) ≤ (N : ℝ).sqrt + (0.98183 : ℝ) * (N : ℝ) ^ (4⁻¹ : ℝ) + C := by
  sorry

/--
Singer's construction [Si38] shows $h(N) \ge (1 - o(1)) N^{1/2}$ for all $N$.
-/
@[category research solved, AMS 11]
theorem erdos_30.variants.singer :
    ∀ ε > (0 : ℝ), ∀ᶠ N : ℕ in atTop, (1 - ε) * (N : ℝ).sqrt ≤ h N := by
  sorry

/--
Combining Singer's lower bound [Si38] with the Erdős–Turán upper bound [ErTu41]:
$h(N) \sim N^{1/2}$.
-/
@[category research solved, AMS 11]
theorem erdos_30.variants.isEquivalent_sqrt :
    (fun N => (h N : ℝ)) ~[atTop] fun N => (N : ℝ).sqrt := by
  sorry

end Erdos30
