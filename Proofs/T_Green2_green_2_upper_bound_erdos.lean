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
# Ben Green's Open Problem 2

References:
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.2)
- [Er65] P. Erdős. Extremal problems in number theory, In Proc. Sympos. Pure Math., Vol. VIII,
  pages 181–189. Amer. Math. Soc., Providence, R.I., 1965.
- [Sa21] Sanders, Tom. "The Erdős–Moser Sum-free Set Problem." Canadian Journal of Mathematics 73.1
  (2021): 63-107.
- [Ru05] I. Z. Ruzsa, Sum-avoiding subsets. Ramanujan J., 9 (2005) (1-2):77–82.
- [Ch71] S. L. G. Choi. On a combinatorial problem in number theory. Proc. London Math. Soc. (3),
  23:629–642, 1971. doi:10.1112/plms/s3-23.4.629.
- [BSS00] A. Baltz, T. Schoen, and A. Srivastav. Probabilistic construction of small strongly
  sum-free sets via large Sidon sets. Colloq. Math., 86(2):171–176, 2000.
  doi:10.4064/cm-86-2-171-176.
-/

@[expose] public section

open Filter
open scoped Topology

namespace Green2



/--
We define the construction from [Sa21, p1] as
$M(A) := \max \{|S| : S \subseteq A \text{ and } (S \hat{+} S) \cap A = \varnothing \}$.
-/
def maxRestrictedSumAvoidingSubsetSize (A : Finset ℤ) : ℕ :=
  (A.powerset.filter fun S => Disjoint S.restrictedSumset A).sup Finset.card

/--
Let $A \subset \mathbf{Z}$ be a set of $n$ integers. Is there a set $S \subset A$ of size
$(\log n)^{100}$ such that the restricted sumset$S \hat{+} S$ is disjoint from $A$?
-/
@[category research open, AMS 11]
theorem green_2 : answer(sorry) ↔
    ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℤ, A.card = n →
      (maxRestrictedSumAvoidingSubsetSize A : ℝ) ≥ (Real.log n) ^ 100 := by
  sorry

/--
From [Sa21] it is known that there is always such an S with $|S| \gt (\log |A|)^{1+c}$.
-/
@[category research solved, AMS 11]
theorem green_2_lower_bound_sanders :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℤ, A.card = n →
      maxRestrictedSumAvoidingSubsetSize A ≥ Real.log n ^ (1 + c) := by
  sorry

open Finset in
lemma g2_pos (S : Finset ℤ) (B : ℤ) (hB : 0 ≤ B) (hS : ∀ x ∈ S, 1 ≤ x ∧ x ≤ B)
    (hsum : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → B < x + y) : 2 * (#S : ℤ) ≤ B + 2 := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp; have := hS; omega
  set m := S.min' hne
  have hm : m ∈ S := S.min'_mem hne
  have hmin : ∀ x ∈ S, m ≤ x := fun x hx => S.min'_le x hx
  have hsub : S.erase m ⊆ Finset.Icc (max (m + 1) (B - m + 1)) B := by
    intro x hx
    obtain ⟨hxm, hxS⟩ := Finset.mem_erase.mp hx
    rw [Finset.mem_Icc]
    have h1 := hmin x hxS
    have h2 := hsum m hm x hxS (Ne.symm hxm)
    exact ⟨max_le (by omega) (by omega), (hS x hxS).2⟩
  have hc := Finset.card_le_card hsub
  rw [Int.card_Icc, Finset.card_erase_of_mem hm] at hc
  have hm1 := (hS m hm).1
  have hpos : 0 < #S := Finset.card_pos.mpr hne
  have : ((#S - 1 : ℕ) : ℤ) ≤ ((B + 1 - max (m + 1) (B - m + 1)).toNat : ℤ) := by exact_mod_cast hc
  rw [Nat.cast_sub hpos] at this
  have htn : ((B + 1 - max (m + 1) (B - m + 1)).toNat : ℤ) ≤ max 0 (B + 1 - max (m + 1) (B - m + 1)) := by
    rw [Int.toNat_eq_max, max_comm]
  push_cast at this
  have hmB := (hS m hm).2
  have hmx1 : m + 1 ≤ max (m + 1) (B - m + 1) := le_max_left _ _
  have hmx2 : B - m + 1 ≤ max (m + 1) (B - m + 1) := le_max_right _ _
  rcases le_total 0 (B + 1 - max (m + 1) (B - m + 1)) with h | h
  · rw [max_eq_right h] at htn; omega
  · rw [max_eq_left h] at htn; omega

open Finset in
lemma g2_bound (n : ℕ) (hn : 1 ≤ n) (S : Finset ℤ)
    (hS : S ⊆ Icc (-((n / 2 : ℕ) : ℤ)) ((n - 1 - n / 2 : ℕ) : ℤ))
    (hdisj : Disjoint S.restrictedSumset (Icc (-((n / 2 : ℕ) : ℤ)) ((n - 1 - n / 2 : ℕ) : ℤ))) :
    4 * #S ≤ n + 5 := by
  set a : ℤ := ((n / 2 : ℕ) : ℤ)
  set b : ℤ := ((n - 1 - n / 2 : ℕ) : ℤ)
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := by positivity
  have hab : 2 * a ≤ n ∧ 2 * b ≤ n := by
    constructor
    · have : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
      show (2 : ℤ) * ((n / 2 : ℕ) : ℤ) ≤ n
      exact_mod_cast this
    · have : 2 * (n - 1 - n / 2) ≤ n := by omega
      show (2 : ℤ) * ((n - 1 - n / 2 : ℕ) : ℤ) ≤ n
      exact_mod_cast this
  have hmem : ∀ x ∈ S, -a ≤ x ∧ x ≤ b := fun x hx => mem_Icc.mp (hS hx)
  have hkey : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ (-a ≤ x + y ∧ x + y ≤ b) := by
    intro x hx y hy hxy h
    have hmemsum : x + y ∈ S.restrictedSumset :=
      mem_image.mpr ⟨(x, y), mem_offDiag.mpr ⟨hx, hy, hxy⟩, rfl⟩
    exact disjoint_left.mp hdisj hmemsum (mem_Icc.mpr h)
  have hS2 : 2 * (#S : ℤ) ≤ max a b + 2 := by
    by_cases h0 : (0 : ℤ) ∈ S
    · have hsub : S ⊆ {0} := by
        intro x hx
        by_contra hx0
        rw [mem_singleton] at hx0
        apply hkey 0 h0 x hx (Ne.symm hx0)
        have := hmem x hx; constructor <;> linarith
      have := card_le_card hsub
      rw [card_singleton] at this
      have : (#S : ℤ) ≤ 1 := by exact_mod_cast this
      have : 0 ≤ max a b := le_max_of_le_left ha
      linarith
    · by_cases hp : ∃ x ∈ S, 0 < x
      · have hall : ∀ y ∈ S, 0 < y := by
          intro y hy
          by_contra hy0
          have hyneg : y < 0 := lt_of_le_of_ne (not_lt.mp hy0) (fun h => h0 (h ▸ hy))
          obtain ⟨x, hx, hxpos⟩ := hp
          apply hkey x hx y hy (by intro h; subst h; linarith)
          have := hmem x hx; have := hmem y hy; constructor <;> linarith
        have := g2_pos S b hb (fun x hx => ⟨hall x hx, (hmem x hx).2⟩) (fun x hx y hy hxy => by
          have h := hkey x hx y hy hxy
          have := hall x hx; have := hall y hy
          by_contra hle; push Not at hle; exact h ⟨by linarith, hle⟩)
        have := le_max_right a b; linarith
      · push Not at hp
        have hall : ∀ y ∈ S, y < 0 := fun y hy =>
          lt_of_le_of_ne (hp y hy) (fun h => h0 (h ▸ hy))
        have hinj : Set.InjOn (fun x : ℤ => -x) (S : Set ℤ) := fun x _ y _ h => by simpa using h
        have hc : #(S.image fun x => -x) = #S := card_image_of_injOn hinj
        have := g2_pos (S.image fun x => -x) a ha (by
          intro z hz
          obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
          have := hall x hx; have := (hmem x hx).1
          constructor <;> linarith) (by
          intro z hz w hw hzw
          obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
          obtain ⟨y, hy, rfl⟩ := mem_image.mp hw
          have hxy : x ≠ y := fun h => hzw (by rw [h])
          have h := hkey x hx y hy hxy
          have := hall x hx; have := hall y hy
          by_contra hle; push Not at hle; exact h ⟨by linarith, by linarith⟩)
        rw [hc] at this
        have := le_max_left a b; linarith
  have : 4 * (#S : ℤ) ≤ n + 5 := by
    rcases le_total a b with h | h
    · rw [max_eq_right h] at hS2; linarith [hab.2]
    · rw [max_eq_left h] at hS2; linarith [hab.1]
  exact_mod_cast this

open Finset in
theorem g2_main : ∃ C : ℝ, ∀ᶠ n : ℕ in Filter.atTop, ∃ A : Finset ℤ, A.card = n ∧
    (maxRestrictedSumAvoidingSubsetSize A : ℝ) ≤ A.card / 3 + C := by
  refine ⟨2, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  refine ⟨Icc (-((n / 2 : ℕ) : ℤ)) ((n - 1 - n / 2 : ℕ) : ℤ), ?_, ?_⟩
  · rw [Int.card_Icc]; omega
  · have hcard : #(Icc (-((n / 2 : ℕ) : ℤ)) ((n - 1 - n / 2 : ℕ) : ℤ)) = n := by
      rw [Int.card_Icc]; omega
    rw [hcard]
    have hsup : maxRestrictedSumAvoidingSubsetSize (Icc (-((n / 2 : ℕ) : ℤ)) ((n - 1 - n / 2 : ℕ) : ℤ))
        ≤ (n + 5) / 4 := by
      apply Finset.sup_le
      intro S hS
      rw [mem_filter, mem_powerset] at hS
      rw [Nat.le_div_iff_mul_le (by norm_num), mul_comm]
      exact g2_bound n hn S hS.1 hS.2
    have h1 : ((maxRestrictedSumAvoidingSubsetSize
        (Icc (-((n / 2 : ℕ) : ℤ)) ((n - 1 - n / 2 : ℕ) : ℤ)) : ℕ) : ℝ) ≤ (((n + 5) / 4 : ℕ) : ℝ) := by
      exact_mod_cast hsup
    have h2 : (((n + 5) / 4 : ℕ) : ℝ) ≤ ((n : ℝ) + 5) / 4 := by
      rw [le_div_iff₀ (by norm_num)]
      have : (n + 5) / 4 * 4 ≤ n + 5 := Nat.div_mul_le_self _ _
      exact_mod_cast this
    have h3 : ((n : ℝ) + 5) / 4 ≤ (n : ℝ) / 3 + 2 := by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    linarith

/--
From [Er65] it is known that $M(A) \le \frac{1}{3}|A| + O(1)$.
-/
@[category research solved, AMS 11]
theorem green_2_upper_bound_erdos :
    ∃ C : ℝ, ∀ᶠ n in atTop, ∃ A : Finset ℤ, A.card = n ∧
      (maxRestrictedSumAvoidingSubsetSize A : ℝ) ≤ A.card / 3 + C := by
  exact g2_main

/-
TODO(jeangud): Add additional bounds on non-negative integers from Selfridge [Er65, p187], and
Choi [Er65, p190], and [BSS00].
-/

/--
From [Ch71] it is known that $M(A) \le |A|^{2/5 + o(1)}$.
-/
@[category research solved, AMS 11]
theorem green_2_upper_bound_choi :
    ∃ (o : ℕ → ℝ) (_ : Tendsto o atTop (𝓝 0)), ∀ᶠ n in atTop, ∃ A : Finset ℤ, A.card = n ∧
      (maxRestrictedSumAvoidingSubsetSize A : ℝ) ≤ A.card ^ (2 / 5 + o A.card) := by
  sorry

/--
From [Ru05] the best-known upper bound is $|S| \lt e^{C \sqrt{\log |A|}}$.
-/
@[category research solved, AMS 11]
theorem green_2_upper_bound_ruzsa :
    ∃ C > (0 : ℝ), ∀ᶠ n in atTop, ∃ A : Finset ℤ, A.card = n ∧
      (maxRestrictedSumAvoidingSubsetSize A : ℝ) < Real.exp (C * Real.sqrt (Real.log A.card)) := by
  sorry

end Green2
