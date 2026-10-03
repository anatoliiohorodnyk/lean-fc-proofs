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
# Erdős Problem 357

*References:*
- [erdosproblems.com/357](https://www.erdosproblems.com/357)
- [He86] Hegyvári, Norbert, On consecutive sums in sequences. Acta Math. Hungar. (1986), 193--200.
-/

@[expose] public section

namespace Erdos357

open Filter Asymptotics

def HasDistinctSums {ι α : Type*} [Preorder ι] [AddCommMonoid α] (a : ι → α) : Prop :=
  {J : Finset ι | (J : Set ι).OrdConnected}.InjOn (fun J ↦ ∑ x ∈ J, a x)

/-- Let $f(n)$ be the maximal $k$ such that there exist integers $1 \le a_1 < \dotsc < a_k \le n$
such that all sums of the shape $\sum_{u \le i \le v} a_i$ are distinct. -/
noncomputable def f (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ a : Fin k → ℤ, Set.range a ⊆ Set.Icc 1 n ∧ StrictMono a ∧ HasDistinctSums a}

/-- Let $f(n)$ be the maximal $k$ such that there exist integers $1 \le a_1 < \dotsc < a_k \le n$
such that all sums of the shape $\sum_{u \le i \le v} a_i$ are distinct. Is $f(n)=o(n)$? -/
@[category research open, AMS 11]
theorem erdos_357.parts.i : (fun n ↦ (f n : ℝ)) =o[atTop] (fun n ↦ (n : ℝ)) := by
  sorry

/-
Formalisation note: the next 5 formalisations are an attempt at capturing the question "how does
$f(n)$ grow?". In addition to trivial solutions (e.g. setting `answer(sorry) = 0` in some of these),
it is possible that some of these admit easy solutions that shouldn't count as genuine solutions.
As usual in this repo, solving this problem is not simply providing a term to replace `answer(sorry)`
together with a proof of the theorem, but providing a *mathematically interesting* answer.
Note also that there might be other reasonable (and non equivalent) formal statements that capture this
question.
Similar remarks hold for the `variants.monotone` formalisations later in this file.
-/

/-- Let $f(n)$ be the maximal $k$ such that there exist integers $1 \le a_1 < \dotsc < a_k \le n$
such that all sums of the shape $\sum_{u \le i \le v} a_i$ are distinct.
How does $f(n)$ grow? Can we find a (good) explicit function $g$ such that $g = O(f)$ ? -/
@[category research open, AMS 11]
theorem erdos_357.parts.ii.bigO_version :
    (answer(sorry) : ℕ → ℝ) =O[atTop] (fun n ↦ (f n : ℝ)) := by
  sorry

/-- Let $f(n)$ be the maximal $k$ such that there exist integers $1 \le a_1 < \dotsc < a_k \le n$
such that all sums of the shape $\sum_{u \le i \le v} a_i$ are distinct.
How does $f(n)$ grow? Can we find a (good) explicit function $g$ such that $f = O(g)$ ? -/
@[category research open, AMS 11]
theorem erdos_357.parts.ii.bigO_version_symm :
    (fun n ↦ (f n : ℝ)) =O[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

/-- Let $f(n)$ be the maximal $k$ such that there exist integers $1 \le a_1 < \dotsc < a_k \le n$
such that all sums of the shape $\sum_{u \le i \le v} a_i$ are distinct.
How does $f(n)$ grow? Can we find a (good) explicit function $g$ such that $f = \Theta(g)$ ? -/
@[category research open, AMS 11]
theorem erdos_357.parts.ii.bigTheta_version :
    (fun n ↦ (f n : ℝ)) =Θ[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

/-- Let $f(n)$ be the maximal $k$ such that there exist integers $1 \le a_1 < \dotsc < a_k \le n$
such that all sums of the shape $\sum_{u \le i \le v} a_i$ are distinct.
How does $f(n)$ grow? Can we find a (good) explicit function $g$ such that $g = o(f)$ ? -/
@[category research open, AMS 11]
theorem erdos_357.parts.ii.littleO_version :
    (answer(sorry) : ℕ → ℝ) =o[atTop] (fun n ↦ (f n : ℝ)) := by
  sorry

/-- Let $f(n)$ be the maximal $k$ such that there exist integers $1 \le a_1 < \dotsc < a_k \le n$
such that all sums of the shape $\sum_{u \le i \le v} a_i$ are distinct.
How does $f(n)$ grow? Can we find a (good) explicit function $g$ such that $f = o(g)$ ? -/
@[category research open, AMS 11]
theorem erdos_357.parts.ii.littleO_version_symm :
    (fun n ↦ (f n : ℝ)) =o[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

/-- An order-connected nonempty finset of `Fin k` is the interval between its min and max. -/
lemma e357_icc {k : ℕ} (J : Finset (Fin k)) (hJ : (J : Set (Fin k)).OrdConnected)
    (hne : J.Nonempty) : J = Finset.Icc (J.min' hne) (J.max' hne) := by
  ext i
  simp only [Finset.mem_Icc]
  constructor
  · intro hi; exact ⟨J.min'_le i hi, J.le_max' i hi⟩
  · rintro ⟨h1, h2⟩
    exact hJ.out (J.min'_mem hne) (J.max'_mem hne) ⟨h1, h2⟩

/-- Sum of `x + 1 + i` over an interval `[u, u + r)` of naturals. -/
lemma e357_sum_nat (x u r : ℕ) :
    2 * ∑ m ∈ Finset.Ico u (u + r), (x + 1 + m) = 2 * r * (x + 1 + u) + r * (r - 1) := by
  rw [Finset.sum_Ico_eq_sum_range, show u + r - u = r by omega]
  have h1 : ∀ r : ℕ, ∑ t ∈ Finset.range r, (x + 1 + (u + t)) =
      r * (x + 1 + u) + ∑ t ∈ Finset.range r, t := by
    intro r
    induction r with
    | zero => simp
    | succ r ih => rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]; ring
  rw [h1, mul_add, mul_comm 2 (∑ t ∈ Finset.range r, t), Finset.sum_range_id_mul_two r]
  ring
lemma e357_sumJ {k : ℕ} (x : ℕ) (J : Finset (Fin k)) (hJ : (J : Set (Fin k)).OrdConnected)
    (hne : J.Nonempty) :
    2 * ∑ i ∈ J, (x + 1 + (i : ℕ)) =
      2 * J.card * (x + 1 + (J.min' hne : ℕ)) + J.card * (J.card - 1) ∧
    (J.min' hne : ℕ) + J.card ≤ k ∧ (J.max' hne : ℕ) + 1 = (J.min' hne : ℕ) + J.card := by
  set m := J.min' hne
  set M := J.max' hne
  have hmM : m ≤ M := J.min'_le_max' hne
  have hJ' := e357_icc J hJ hne
  have hcard : J.card = (M : ℕ) + 1 - m := by
    rw [hJ', Fin.card_Icc]
  have hmM' : (m : ℕ) ≤ M := hmM
  refine ⟨?_, ?_, ?_⟩
  · have hsum : ∑ i ∈ J, (x + 1 + (i : ℕ)) = ∑ t ∈ Finset.Ico (m : ℕ) ((m : ℕ) + J.card), (x + 1 + t) := by
      rw [hJ']
      rw [show ∑ i ∈ Finset.Icc m M, (x + 1 + (i : ℕ)) =
          ∑ t ∈ (Finset.Icc m M).map Fin.valEmbedding, (x + 1 + t) by rw [Finset.sum_map]; rfl]
      rw [Fin.map_valEmbedding_Icc, ← hJ', hcard]
      congr 1
      ext t; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [hsum, e357_sum_nat]
  · have := M.isLt; omega
  · omega

lemma e357_T_lt (x k u r u' r' : ℕ) (hx : k ^ 2 + 1 ≤ 4 * x) (hr : 1 ≤ r)
    (hu : u + r ≤ k) (hu' : u' + r' ≤ k) (hrr : r < r') :
    2 * r * (x + 1 + u) + r * (r - 1) < 2 * r' * (x + 1 + u') + r' * (r' - 1) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  obtain ⟨s', rfl⟩ : ∃ s', r' = s' + 1 := ⟨r' - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hss : s + 1 ≤ s' := by omega
  have hk : u ≤ k - (s + 1) := by omega
  zify [hss] at *
  have hk2 : (u : ℤ) + s + 1 ≤ k := by push_cast at hu; linarith
  nlinarith [sq_nonneg ((k : ℤ) - 2 * (s + 1)), sq_nonneg ((s' : ℤ) - s - 1)]

lemma e357_T_inj (x k u r u' r' : ℕ) (hx : k ^ 2 + 1 ≤ 4 * x) (hr : 1 ≤ r) (hr' : 1 ≤ r')
    (hu : u + r ≤ k) (hu' : u' + r' ≤ k)
    (h : 2 * r * (x + 1 + u) + r * (r - 1) = 2 * r' * (x + 1 + u') + r' * (r' - 1)) :
    r = r' ∧ u = u' := by
  rcases lt_trichotomy r r' with hlt | heq | hgt
  · exact absurd h (e357_T_lt x k u r u' r' hx hr hu hu' hlt).ne
  · subst heq
    refine ⟨rfl, ?_⟩
    have : 2 * r * (x + 1 + u) = 2 * r * (x + 1 + u') := by omega
    have h2 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2 * r) this
    omega
  · exact absurd h.symm (e357_T_lt x k u' r' u r hx hr' hu' hu hgt).ne

lemma e357_distinct (k x : ℕ) (hx : k ^ 2 + 1 ≤ 4 * x) :
    HasDistinctSums (fun i : Fin k => ((x + 1 + (i : ℕ) : ℕ) : ℤ)) := by
  intro J hJ J' hJ' heq
  simp only [Set.mem_setOf_eq] at hJ hJ'
  simp only at heq
  rw [← Nat.cast_sum, ← Nat.cast_sum, Nat.cast_inj] at heq
  rcases J.eq_empty_or_nonempty with hJe | hne
  · subst hJe
    rw [Finset.sum_empty] at heq
    symm
    by_contra hne'
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hne'
    have := Finset.single_le_sum (f := fun i : Fin k => x + 1 + (i : ℕ)) (fun _ _ => Nat.zero_le _) hi
    omega
  rcases J'.eq_empty_or_nonempty with hJe' | hne'
  · subst hJe'
    rw [Finset.sum_empty] at heq
    obtain ⟨i, hi⟩ := hne
    have := Finset.single_le_sum (f := fun i : Fin k => x + 1 + (i : ℕ)) (fun _ _ => Nat.zero_le _) hi
    omega
  obtain ⟨h1, h2, h3⟩ := e357_sumJ x J hJ hne
  obtain ⟨h1', h2', h3'⟩ := e357_sumJ x J' hJ' hne'
  have hr : 1 ≤ J.card := Finset.card_pos.mpr hne
  have hr' : 1 ≤ J'.card := Finset.card_pos.mpr hne'
  obtain ⟨hcard, hmin⟩ := e357_T_inj x k _ _ _ _ hx hr hr' h2 h2' (by rw [← h1, ← h1', heq])
  have hmin' : J.min' hne = J'.min' hne' := Fin.ext hmin
  have hmax' : J.max' hne = J'.max' hne' := Fin.ext (by omega)
  rw [e357_icc J hJ hne, e357_icc J' hJ' hne', hmin', hmax']

lemma e357_bdd (n : ℕ) :
    BddAbove {k : ℕ | ∃ a : Fin k → ℤ, Set.range a ⊆ Set.Icc 1 n ∧ StrictMono a ∧ HasDistinctSums a} := by
  refine ⟨n, fun k hk => ?_⟩
  obtain ⟨a, hr, hmono, -⟩ := hk
  have h := Finset.card_le_card_of_injOn a (s := Finset.univ) (t := Finset.Icc (1 : ℤ) n)
    (fun i _ => by
      have := hr ⟨i, rfl⟩
      simpa [Finset.mem_Icc] using this) hmono.injective.injOn
  simpa using h

lemma e357_le_f (n k x : ℕ) (hx : k ^ 2 + 1 ≤ 4 * x) (hn : x + k ≤ n) : k ≤ f n := by
  apply le_csSup (e357_bdd n)
  refine ⟨fun i : Fin k => ((x + 1 + (i : ℕ) : ℕ) : ℤ), ?_, ?_, e357_distinct k x hx⟩
  · rintro _ ⟨i, rfl⟩
    have := i.isLt
    simp only [Set.mem_Icc]
    constructor <;> push_cast <;> omega
  · intro i j hij
    simp only
    have : (i : ℕ) < j := hij
    push_cast; omega

/-- Let $f(n)$ be the maximal $k$ such that there exist integers $1 \le a_1 < \dotsc < a_k \le n$
such that all sums of the shape $\sum_{u \le i \le v} a_i$ are distinct.
It is known that $f(n) \geq (2+o(1))\sqrt{n}$.
Source: See comment by Desmond Weisenberg here: https://www.erdosproblems.com/forum/thread/357.
-/
@[category research solved, AMS 11]
theorem erdos_357.variants.weisenberg : ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ᶠ n in atTop, (2 + o n) * √n ≤ f n := by
  refine ⟨fun n => -3 / √n, ?_, ?_⟩
  · rw [show (1 : ℕ → ℝ) = fun _ => (1 : ℝ) from rfl, Asymptotics.isLittleO_one_iff]
    have hs : Tendsto (fun n : ℕ => √(n : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    exact hs.const_div_atTop (-3)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    set s := Nat.sqrt (4 * n) with hsdef
    have hs1 : s * s ≤ 4 * n := Nat.sqrt_le (4 * n)
    have hs2 : 4 * n < (s + 1) * (s + 1) := Nat.lt_succ_sqrt (4 * n)
    have hn0 : (0 : ℝ) < √n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    have hsq : √(n : ℝ) * √n = n := Real.mul_self_sqrt (by positivity)
    -- (s + 1) > 2√n
    have hsR : 2 * √(n : ℝ) < s + 1 := by
      have h4 : (4 * n : ℝ) < ((s + 1) * (s + 1) : ℕ) := by exact_mod_cast hs2
      push_cast at h4
      nlinarith [sq_nonneg (2 * √(n : ℝ) - (s + 1))]
    rw [show (2 + -3 / √(n : ℝ)) * √n = 2 * √n - 3 by field_simp; ring]
    rcases Nat.lt_or_ge s 2 with hs | hs
    · have : (s : ℝ) < 2 := by exact_mod_cast hs
      have : (0 : ℝ) ≤ f n := by positivity
      linarith
    · set k := s - 2
      have hk := e357_le_f n k ((k ^ 2 + 4) / 4) (by omega) (by
        have : (k + 2) * (k + 2) ≤ 4 * n := by rw [show k + 2 = s by omega]; exact hs1
        have : (k ^ 2 + 4) / 4 * 4 ≤ k ^ 2 + 4 := Nat.div_mul_le_self _ _
        nlinarith)
      have hkR : (k : ℝ) ≤ f n := by exact_mod_cast hk
      have hks : (k : ℝ) = s - 2 := by rw [Nat.cast_sub hs]; push_cast; ring
      linarith

/-- Suppose $A$ is an infinite set such that all finite sums of consecutive terms of $A$ are distinct.
Then $A$ has lower density 0. -/
@[category research solved, AMS 11]
theorem erdos_357.variants.infinite_set_lower_density (A : ℕ → ℕ) (hA : StrictMono A)
    (hA : HasDistinctSums A) : (Set.range A).lowerDensity = 0 := by
  sorry

/--  Suppose $A$ is an infinite set such that all finite sums of consecutive terms of $A$ are distinct.
Then it is conjectured that $A$ has density 0. -/
@[category research open, AMS 11]
theorem erdos_357.variants.infinite_set_density (A : ℕ → ℕ) (hA : StrictMono A)
    (hA : HasDistinctSums A) :
    (Set.range A).HasDensity 0 := by
  sorry


/-- Suppose $A$ is an infinite set such that all finite sums of consecutive terms of $A$ are distinct.
Then it is conjectured that the sum $\sum_k \frac{1}{a_k}$ converges. -/
@[category research open, AMS 11]
theorem erdos_357.variants.infinite_set_sum (A : ℕ → ℕ) (hA : StrictMono A)
    (hA : HasDistinctSums A) :
    Summable (fun i ↦ (1 : ℝ) / A i) := by
  sorry

/-- Let $g(n)$ be the maximal $k$ such that there exist integers $1 \le a_1, \dotsc, a_k \le n$
such that all sums of the shape $\sum_{u \le i \le v} a_i$ are distinct. -/
noncomputable def g (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ a : Fin k → ℕ, (Set.range a ⊆ Set.Icc 1 n) ∧ HasDistinctSums a}

/-- Let $g(n)$ be the maximal $k$ such that there exist integers $1 \le a_1, \dotsc, a_k \le n$
such that all sums of the shape $\sum_{u \le i \le v} a_i$ are distinct. Hegyvári [He86] proved
that
$$\left(\frac 1 3 + o(1) \right)n \leq g(n) \leq \left(\frac 2 3 + o(1) \right)n.$$ -/
@[category research solved, AMS 11]
theorem erdos_357.variants.hegyvari : ∃ (o o' : ℕ → ℝ), o =o[atTop] (1 : ℕ → ℝ) ∧
    o' =o[atTop] (1 : ℕ → ℝ) ∧
      ∀ᶠ n in atTop, (g n : ℝ) ∈ Set.Icc ((1 / 3 + o n) * n) ((2 / 3 + o' n)*n) := by
  sorry

/-- Let $h(n)$ be the maximal $k$ such that there exist integers $1 \le a_1 \leq \dotsc \leq a_k \le n$
such that all sums of the shape $\sum_{u \le i \le v} a_i$ are distinct. -/
noncomputable def h (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ a : Fin k → ℤ, Set.range a ⊆ Set.Icc 1 n ∧ Monotone a ∧ HasDistinctSums a}

-- The analogous question assuming only monotonicity of the $a_i$. The wording of the website
-- suggests that this is open, though it's not clear whether the difficulty is the same as for the
-- strictly monotone case.

/-- Let $h(n)$ be the maximal $k$ such that there exist integers $1 \le a_1 \leq \dotsc \leq a_k \le n$
such that all sums of the shape $\sum_{u \le i \le v} a_i$ are distinct. Is $h(n)=o(n)$? -/
@[category research open, AMS 11]
theorem erdos_357.variants.monotone.parts.i : (fun n ↦ (h n : ℝ)) =o[atTop] (fun n ↦ (n : ℝ)) := by
  sorry

/-- Let $h(n)$ be the maximal $k$ such that there exist integers $1 \le a_1 \leq \dotsc \leq a_k \le n$
such that all sums of the shape $\sum_{u \le i \le v} a_i$ are distinct. How does $h(n)$ grow?
Can we find a (good) explicit function $g$ such that $g = O(h)$ ? -/
@[category research open, AMS 11]
theorem erdos_357.variants.monotone.parts.ii.bigO_version :
    (answer(sorry) : ℕ → ℝ) =O[atTop] (fun n ↦ (h n : ℝ)) := by
  sorry

/-- Let $h(n)$ be the maximal $k$ such that there exist integers $1 \le a_1 \leq \dotsc \leq a_k \le n$
such that all sums of the shape $\sum_{u \le i \le v} a_i$ are distinct. How does $h(n)$ grow?
Can we find a (good) explicit function $g$ such that $h = O(g)$ ? -/
@[category research open, AMS 11]
theorem erdos_357.variants.monotone.parts.ii.bigO_version_symm :
    (fun n ↦ (h n : ℝ)) =O[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

/-- Let $h(n)$ be the maximal $k$ such that there exist integers $1 \le a_1 \leq \dotsc \leq a_k \le n$
such that all sums of the shape $\sum_{u \le i \le v} a_i$ are distinct. How does $h(n)$ grow?
Can we find a (good) explicit function $g$ such that $h = \Theta(g)$ ? -/
@[category research open, AMS 11]
theorem erdos_357.variants.monotone.parts.ii.bigTheta_version :
    (fun n ↦ (h n : ℝ)) =Θ[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

/-- Let $h(n)$ be the maximal $k$ such that there exist integers $1 \le a_1 \leq \dotsc \leq a_k \le n$
such that all sums of the shape $\sum_{u \le i \le v} a_i$ are distinct. How does $h(n)$ grow?
Can we find a (good) explicit function $g$ such that $g = o(h)$ ? -/
@[category research open, AMS 11]
theorem erdos_357.variants.monotone.parts.ii.littleO_version :
    (answer(sorry) : ℕ → ℝ) =o[atTop] (fun n ↦ (h n : ℝ)) := by
  sorry

/-- Let $h(n)$ be the maximal $k$ such that there exist integers $1 \le a_1 \leq \dotsc \leq a_k \le n$
such that all sums of the shape $\sum_{u \le i \le v} a_i$ are distinct. How does $h(n)$ grow?
Can we find a (good) explicit function $g$ such that $h = o(g)$ ? -/
@[category research open, AMS 11]
theorem erdos_357.variants.monotone.parts.ii.littleO_version_symm :
    (fun n ↦ (h n : ℝ)) =o[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

-- TODO(Paul-Lez): add results from last paragraph of the page.

end Erdos357
