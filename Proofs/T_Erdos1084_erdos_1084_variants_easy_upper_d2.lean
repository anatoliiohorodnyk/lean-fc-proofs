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
# Erdős Problem 1084

*References:*
- [erdosproblems.com/1084](https://www.erdosproblems.com/1084)
- [Ha74b] Harborth, Heiko, Lösung zu Problem 664A. Elem. Math. (1974), 14--15.

Let `f_2(n)` be the maximum number of pairs of points at distance exactly `1`
among any set of `n` points in `ℝ²`, under the condition that all pairwise
distances are at least `1`.

Estimate the growth of `f_2(n)`.

Status: open.
-/

@[expose] public section

open Finset Filter Metric Real
open scoped EuclideanGeometry

namespace Erdos1084
variable {n : ℕ}

/-- The maximal number of pairs of points which are distance 1 apart that a set of `n` 1-separated
points in `ℝ^d` make. -/
noncomputable def f (d n : ℕ) : ℕ :=
  ⨆ (s : Finset (ℝ^ d)) (_ : s.card = n) (_ : IsSeparated' 1 (s : Set (ℝ^ d))), unitDistNum s

-- TODO: Add erdos_1084.

/-- It is easy to check that $f_1(n) = n - 1$. -/
@[category research solved, AMS 52, formal_proof using formal_conjectures at "https://github.com/Sanexxxx777/formal-conjectures/blob/9e4f3845be122a8fa3190d38543ebdd0a6f25605/FormalConjectures/ErdosProblems/1084.lean#L232"]
theorem erdos_1084.variants.upper_d1 : f 1 n = n - 1 := by
  sorry

lemma e1084_dist_lt (z w : ℂ) (hz : ‖z‖ = 1) (hw : ‖w‖ = 1)
    (h : |Complex.arg z - Complex.arg w| < π / 3) : ‖z - w‖ < 1 := by
  have hz0 : z ≠ 0 := by intro h0; rw [h0, norm_zero] at hz; norm_num at hz
  have hw0 : w ≠ 0 := by intro h0; rw [h0, norm_zero] at hw; norm_num at hw
  have hcz : Real.cos (Complex.arg z) = z.re := by rw [Complex.cos_arg hz0, hz, div_one]
  have hsz : Real.sin (Complex.arg z) = z.im := by rw [Complex.sin_arg, hz, div_one]
  have hcw : Real.cos (Complex.arg w) = w.re := by rw [Complex.cos_arg hw0, hw, div_one]
  have hsw : Real.sin (Complex.arg w) = w.im := by rw [Complex.sin_arg, hw, div_one]
  have hz2 : z.re ^ 2 + z.im ^ 2 = 1 := by
    have := Complex.sq_norm z; rw [hz, Complex.normSq_apply] at this; nlinarith
  have hw2 : w.re ^ 2 + w.im ^ 2 = 1 := by
    have := Complex.sq_norm w; rw [hw, Complex.normSq_apply] at this; nlinarith
  have hcos : 1 / 2 < Real.cos (Complex.arg z - Complex.arg w) := by
    rw [← Real.cos_abs, ← Real.cos_pi_div_three]
    apply Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) h
  rw [Real.cos_sub, hcz, hsz, hcw, hsw] at hcos
  have hsq : ‖z - w‖ ^ 2 < 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im]
    nlinarith
  nlinarith [norm_nonneg (z - w)]

/-- Sector index in `{1, …, 6}`. -/
noncomputable def e1084sec (θ : ℝ) : ℤ := ⌈(θ + π) / (π / 3)⌉

lemma e1084_sec_mem (z : ℂ) : e1084sec (Complex.arg z) ∈ Finset.Icc (1 : ℤ) 6 := by
  have h1 := Complex.neg_pi_lt_arg z
  have h2 := Complex.arg_le_pi z
  have hp := Real.pi_pos
  rw [Finset.mem_Icc, e1084sec]
  constructor
  · rw [Int.one_le_ceil_iff]; apply div_pos (by linarith) (by positivity)
  · rw [Int.ceil_le, div_le_iff₀ (by positivity)]; push_cast; linarith

lemma e1084_sec_close (a b : ℝ) (h : e1084sec a = e1084sec b) : |a - b| < π / 3 := by
  have hp : 0 < π / 3 := by positivity
  unfold e1084sec at h
  have ha := Int.ceil_lt_add_one ((a + π) / (π / 3))
  have ha' := Int.le_ceil ((a + π) / (π / 3))
  have hb := Int.ceil_lt_add_one ((b + π) / (π / 3))
  have hb' := Int.le_ceil ((b + π) / (π / 3))
  rw [h] at ha ha'
  have h1 : (a + π) / (π / 3) - (b + π) / (π / 3) < 1 := by linarith
  have h2 : (b + π) / (π / 3) - (a + π) / (π / 3) < 1 := by linarith
  rw [← sub_div, div_lt_one hp] at h1 h2
  rw [abs_lt]; constructor <;> linarith

noncomputable def e1084C (p : EuclideanSpace ℝ (Fin 2)) : ℂ := ⟨p 0, p 1⟩

lemma e1084_dist (p q : EuclideanSpace ℝ (Fin 2)) : dist p q = ‖e1084C p - e1084C q‖ := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, Complex.norm_def, Complex.normSq_apply]
  simp only [e1084C, Complex.sub_re, Complex.sub_im, Real.dist_eq, sq_abs]
  congr 1; ring

lemma e1084_deg (v : EuclideanSpace ℝ (Fin 2)) (N : Finset (EuclideanSpace ℝ (Fin 2)))
    (hN : ∀ w ∈ N, dist w v = 1) (hsep : ∀ w ∈ N, ∀ w' ∈ N, w ≠ w' → 1 ≤ dist w w')
    (T : Finset ℤ) (hT : ∀ w ∈ N, e1084sec (Complex.arg (e1084C w - e1084C v)) ∈ T) :
    #N ≤ #T := by
  apply Finset.card_le_card_of_injOn (fun w => e1084sec (Complex.arg (e1084C w - e1084C v))) hT
  intro w hw w' hw' h
  by_contra hne
  have hclose := e1084_sec_close _ _ h
  have h1 : ‖e1084C w - e1084C v‖ = 1 := by rw [← e1084_dist]; exact hN w hw
  have h2 : ‖e1084C w' - e1084C v‖ = 1 := by rw [← e1084_dist]; exact hN w' hw'
  have := e1084_dist_lt _ _ h1 h2 hclose
  rw [show e1084C w - e1084C v - (e1084C w' - e1084C v) = e1084C w - e1084C w' by ring,
    ← e1084_dist] at this
  linarith [hsep w hw w' hw' hne]

lemma e1084_bottom (v w : EuclideanSpace ℝ (Fin 2)) (hvw : v 1 < w 1 ∨ (v 1 = w 1 ∧ v 0 < w 0)) :
    e1084sec (Complex.arg (e1084C w - e1084C v)) ∈ Finset.Icc (3 : ℤ) 6 := by
  set z := e1084C w - e1084C v
  have hre : z.re = w 0 - v 0 := rfl
  have him : z.im = w 1 - v 1 := rfl
  have h0 : 0 ≤ Complex.arg z := Complex.arg_nonneg_iff.mpr (by
    rw [him]
    rcases hvw with h | h
    · linarith
    · linarith [h.1])
  have hlt : Complex.arg z < π := by
    rcases lt_or_eq_of_le (Complex.arg_le_pi z) with h | h
    · exact h
    · exfalso
      rw [Complex.arg_eq_pi_iff] at h
      rw [hre, him] at h
      rcases hvw with h' | h'
      · linarith [h.2]
      · linarith [h.1, h'.2]
  have hp := Real.pi_pos
  rw [Finset.mem_Icc, e1084sec]
  constructor
  · rw [Int.le_ceil_iff]; push_cast
    rw [lt_div_iff₀ (by positivity)]; linarith
  · rw [Int.ceil_le, div_le_iff₀ (by positivity)]; push_cast; linarith

lemma e1084_handshake (s : Finset (EuclideanSpace ℝ (Fin 2))) :
    2 * unitDistNum s ≤ ∑ v ∈ s, #(s.filter fun w => dist w v = 1) := by
  classical
  set Q := s.sym2.filter fun p => dist p.out.1 p.out.2 = 1
  set P := (s ×ˢ s).filter fun x : _ × _ => dist x.2 x.1 = 1
  have hP : #P = ∑ v ∈ s, #(s.filter fun w => dist w v = 1) := by
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.card_filter]
  have hout : ∀ p ∈ Q, p.out.1 ∈ s ∧ p.out.2 ∈ s ∧ dist p.out.1 p.out.2 = 1 := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_sym2_iff] at hp
    refine ⟨hp.1 _ (Sym2.out_fst_mem p), hp.1 _ (Sym2.out_snd_mem p), hp.2⟩
  let f1 : Sym2 (EuclideanSpace ℝ (Fin 2)) → _ := fun p => (p.out.1, p.out.2)
  let f2 : Sym2 (EuclideanSpace ℝ (Fin 2)) → _ := fun p => (p.out.2, p.out.1)
  have hf1 : Set.InjOn f1 Q := by
    intro p _ q _ h
    simp only [f1, Prod.mk.injEq] at h
    rw [← Quot.out_eq p, ← Quot.out_eq q]
    exact congrArg _ (Prod.ext h.1 h.2)
  have hf2 : Set.InjOn f2 Q := by
    intro p _ q _ h
    simp only [f2, Prod.mk.injEq] at h
    rw [← Quot.out_eq p, ← Quot.out_eq q]
    exact congrArg _ (Prod.ext h.2 h.1)
  have hdisj : Disjoint (Q.image f1) (Q.image f2) := by
    rw [Finset.disjoint_left]
    rintro x hx1 hx2
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx1
    obtain ⟨q, hq, hqx⟩ := Finset.mem_image.mp hx2
    simp only [f1, f2, Prod.mk.injEq] at hqx
    have hpq : p = q := by
      have hsw : Quot.out p = (Quot.out q).swap := Prod.ext hqx.1.symm hqx.2.symm
      rw [← Quot.out_eq p, ← Quot.out_eq q, hsw]
      exact Quot.sound (Sym2.Rel.swap _ _)
    subst hpq
    have h := (hout p hp).2.2
    rw [hqx.2] at h
    simp at h
  have hsub : Q.image f1 ∪ Q.image f2 ⊆ P := by
    intro x hx
    rw [Finset.mem_union] at hx
    rw [Finset.mem_filter, Finset.mem_product]
    rcases hx with hx | hx
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨h1, h2, h3⟩ := hout p hp
      exact ⟨⟨h1, h2⟩, by rw [dist_comm]; exact h3⟩
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨h1, h2, h3⟩ := hout p hp
      exact ⟨⟨h2, h1⟩, h3⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hf1,
    Finset.card_image_of_injOn hf2] at this
  unfold unitDistNum
  change 2 * #Q ≤ _
  omega

lemma e1084_bound (n : ℕ) (hn : n ≠ 0) (s : Finset (EuclideanSpace ℝ (Fin 2))) (hs : #s = n)
    (hsep : Metric.IsSeparated' 1 (s : Set (EuclideanSpace ℝ (Fin 2)))) : unitDistNum s ≤ 3 * n - 1 := by
  classical
  have hsepd : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → 1 ≤ dist x y := by
    intro x hx y hy hxy
    have : 1 ≤ edist x y := hsep hx hy hxy
    rw [edist_dist] at this
    exact (ENNReal.one_le_ofReal).mp this
  set D := fun v => #(s.filter fun w => dist w v = 1)
  have hfilt : ∀ v, ∀ w ∈ s.filter (fun w => dist w v = 1), dist w v = 1 :=
    fun v w hw => (mem_filter.mp hw).2
  have hfsep : ∀ v, ∀ w ∈ s.filter (fun w => dist w v = 1), ∀ w' ∈ s.filter (fun w => dist w v = 1),
      w ≠ w' → 1 ≤ dist w w' :=
    fun v w hw w' hw' => hsepd w (mem_filter.mp hw).1 w' (mem_filter.mp hw').1
  have hD : ∀ v, D v ≤ 6 := fun v => by
    have := e1084_deg v _ (hfilt v) (hfsep v) (Icc 1 6) (fun w _ => e1084_sec_mem _)
    simpa using this
  have hne : s.Nonempty := card_pos.mp (by omega)
  obtain ⟨v0, hv0, hmin⟩ := s.exists_min_image (fun p => toLex (p 1, p 0)) hne
  have hD0 : D v0 ≤ 4 := by
    have := e1084_deg v0 _ (hfilt v0) (hfsep v0) (Icc 3 6) (fun w hw => by
      apply e1084_bottom
      have hws := (mem_filter.mp hw).1
      have hwd := (mem_filter.mp hw).2
      have hle := hmin w hws
      have hne' : w ≠ v0 := by rintro rfl; simp at hwd
      rcases lt_or_eq_of_le hle with hlt | heq
      · rw [Prod.Lex.toLex_lt_toLex] at hlt
        rcases hlt with h | ⟨h1, h2⟩
        · exact Or.inl h
        · exact Or.inr ⟨h1, h2⟩
      · exfalso; apply hne'
        have h := toLex.injective heq
        simp only [Prod.mk.injEq] at h
        ext i; fin_cases i
        · exact h.2.symm
        · exact h.1.symm)
    simpa using this
  have hsum : ∑ v ∈ s, D v ≤ 4 + 6 * (n - 1) := by
    rw [← add_sum_erase s _ hv0]
    have : ∑ v ∈ s.erase v0, D v ≤ ∑ _v ∈ s.erase v0, 6 := sum_le_sum fun v _ => hD v
    rw [sum_const, card_erase_of_mem hv0, hs, smul_eq_mul] at this
    omega
  have hh := e1084_handshake s
  have hrw : ∑ v ∈ s, #(s.filter fun w => dist w v = 1) = ∑ v ∈ s, D v := rfl
  omega

theorem e1084_main (n : ℕ) (hn : n ≠ 0) : f 2 n < 3 * n := by
  have : f 2 n ≤ 3 * n - 1 := by
    unfold f
    exact ciSup_le' fun s => ciSup_le' fun hs => ciSup_le' fun hsep => e1084_bound n hn s hs hsep
  omega

/-- It is easy to check that $f_2(n) < 3n$. -/
@[category research solved, AMS 52]
theorem erdos_1084.variants.easy_upper_d2 (hn : n ≠ 0) : f 2 n < 3 * n := by
  exact e1084_main n hn

/-- Erdős showed that there is some constant $c > 0$ such that $f_2(n) < 3n - c n^{1/2}$. -/
@[category research solved, AMS 52]
theorem erdos_1084.variants.upper_d2 : ∃ c > (0 : ℝ), ∀ n > 0, f 2 n < 3 * n - c * sqrt n := by
  sorry

/-- Erdős conjectured that the triangular lattice is best possible in 2D, in particular that
$f_2(3n^2 + 3n + 1) = 9n^2 + 3n$. Harborth [Ha74b] proved this, and more generally
$f_2(n) = \lfloor 3n - \sqrt{12n - 3} \rfloor$ for all $n \geq 2$.

Note: in [Er75f] is read $9n^2 + 6n$, but this seems to be a typo.
-/
@[category research solved, AMS 52]
theorem erdos_1084.variants.triangular_optimal_d2 : f 2 (3 * n ^ 2 + 3 * n + 1) = 9 * n ^ 2 + 3 * n := by
  sorry

/-- Erdős claims the existence of two constants $c_1, c_2 > 0$
such that $6n - c_1 n^{2/3} ≤ f_3(n) \le 6n - c_2 n^{2/3}$. -/
@[category research solved, AMS 52]
theorem erdos_1084.variants.upper_lower_d3 :
    ∃ c₁ : ℝ, ∃ c₂ > (0 : ℝ), ∀ᶠ n in atTop,
      6 * n - c₁ * n ^ (2 / 3 : ℝ) ≤ f 3 n ∧ f 3 n ≤ 6 * n - c₂ * n ^ (2 / 3 : ℝ) := by
  sorry

end Erdos1084
