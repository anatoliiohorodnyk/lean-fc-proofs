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
# Ben Green's Open Problem 40

*References:*
- [Gr24] [Ben Green's Open Problem 40](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.40)
- [Da90] Davydov, Alexander Abramovich. "Construction of linear covering codes."
  Problemy Peredachi Informatsii 26.4 (1990): 38-55.
- [CHL97] Cohen, G., Honkala, I., Litsyn, S., & Lobstein, A. (1997). Covering codes (Vol. 54). Elsevier.
- [St94] R. Struik, Covering codes, PhD Thesis, Eindhoven University of Technology, the Netherlands, 106 pp, 1994.

-/

@[expose] public section

open Filter Topology Fintype
open scoped ENNReal Pointwise

namespace Green40


/-- The Hamming ball of radius $r$ in $\mathbb{F}_2^n$. -/
def hammingBall (n r : ℕ) : Set (𝔽₂ n) :=
  {x | hammingNorm x ≤ r}

/-- $V$ is a covering subspace of $\mathbb{F}_2^n$ by $H(r)$ if $V + H(r) = \mathbb{F}_2^n$. -/
def IsCoveringSubspace (n r : ℕ) (V : Submodule (ZMod 2) (𝔽₂ n)) : Prop :=
  (V : Set (𝔽₂ n)) + hammingBall n r = Set.univ

/-- The minimal covering density over all covering subspaces for a given n and r.
    We compute in `ℝ≥0∞` (ENNReal) to gracefully handle any potential divergence. -/
noncomputable def minDensity (n r : ℕ) : ℝ≥0∞ :=
  ⨅ (V : Submodule (ZMod 2) (𝔽₂ n)) (_ : IsCoveringSubspace n r V),
    (Nat.card V : ℝ≥0∞) * (Nat.card (hammingBall n r) : ℝ≥0∞) / (2 ^ n : ℝ≥0∞)

/--
Let $f(r)$ be the smallest constant such that there exists an infinite sequence of $n$'s together
with subspaces $V_n \leq \mathbb{F}_2^n$ with $V_n + H(r) = \mathbb{F}_2^n$ and
$|V_n| = \left(f(r) + o(1)\right) \frac{2^n}{|H(r)|}$.
-/
noncomputable def f (r : ℕ) : ℝ≥0∞ :=
  liminf (fun n ↦ minDensity n r) atTop

/-- Does $f(r) \to \infty$? [Gr24]-/
@[category research open, AMS 5 94]
theorem green_40 : answer(sorry) ↔ Tendsto f atTop (𝓝 ⊤) := by
  sorry

/-- The only value known is $f(1) = 1$, which follows from the existence of the Hamming code [Gr24]. -/
@[category research solved, AMS 5 94]
theorem green_40.sanity_f_one : f 1 = 1 := by
  sorry

lemma g40_zmod2 (a : ZMod 2) (h : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact absurd rfl h
  · rfl
lemma g40_two_add {κ : Type} (x : κ → ZMod 2) : x + x = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize x i = a
  fin_cases a <;> rfl

open Finset in
lemma g40u_card_ball_le (n r : ℕ) :
    Nat.card (hammingBall n r) ≤ ∑ i ∈ range (r + 1), n.choose i := by
  classical
  let T : Finset (Finset (Fin n)) := (range (r + 1)).biUnion (fun i => powersetCard i univ)
  let g : hammingBall n r → T := fun x => ⟨univ.filter (fun i => x.1 i ≠ 0), by
    have hx := x.2
    simp only [hammingBall, Set.mem_setOf_eq, hammingNorm] at hx
    simp only [T, mem_biUnion, mem_range, mem_powersetCard, subset_univ, true_and]
    exact ⟨_, Nat.lt_succ_of_le hx, rfl⟩⟩
  have hg : Function.Injective g := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    simp only [g, Subtype.mk.injEq] at h
    ext1
    funext i
    have := congrArg (fun s => i ∈ s) h
    simp only [mem_filter, mem_univ, true_and, eq_iff_iff] at this
    show x i = y i
    by_cases hxi : x i = 0
    · have : y i = 0 := by by_contra hyi; exact this.mpr hyi hxi
      rw [hxi, this]
    · rw [g40_zmod2 _ hxi, g40_zmod2 _ (this.mp hxi)]
  calc Nat.card (hammingBall n r) ≤ Nat.card T := Nat.card_le_card_of_injective g hg
    _ = T.card := by simp
    _ ≤ ∑ i ∈ range (r + 1), (powersetCard i (univ : Finset (Fin n))).card := card_biUnion_le
    _ = ∑ i ∈ range (r + 1), n.choose i := by simp

open Finset in
lemma g40u_sum_choose_le (n r : ℕ) : ∑ i ∈ range (r + 1), n.choose i ≤ (n + r).choose r := by
  rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_le_sum
  intro k hk
  have hk' := Finset.mem_range.mp hk
  exact Nat.le_mul_of_pos_right _ (Nat.choose_pos (by omega))

lemma g40u_choose_fact (N r : ℕ) : N.choose r * r.factorial ≤ N ^ r := by
  rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
  exact Nat.descFactorial_le_pow N r

/-- U4: a parity-check map hitting everything with weight `≤ r` gives a covering code. -/
lemma g40u_gen (n r : ℕ) {ι : Type} [Fintype ι] (H : 𝔽₂ n →ₗ[ZMod 2] (ι → ZMod 2))
    (hH : ∀ s, ∃ y, hammingNorm y ≤ r ∧ H y = s) :
    IsCoveringSubspace n r (LinearMap.ker H) ∧
      Nat.card (LinearMap.ker H) * 2 ^ Fintype.card ι = 2 ^ n := by
  refine ⟨?_, ?_⟩
  · apply Set.eq_univ_of_forall
    intro x
    rw [Set.mem_add]
    obtain ⟨y, hy, hHy⟩ := hH (H x)
    refine ⟨x + y, ?_, y, hy, by rw [add_assoc, g40_two_add, add_zero]⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_add, hHy]
    exact g40_two_add (H x)
  · have hsurj : LinearMap.range H = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro s; obtain ⟨y, _, hy⟩ := hH s; exact ⟨y, hy⟩
    have hrk := LinearMap.finrank_range_add_finrank_ker H
    rw [hsurj, finrank_top] at hrk
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hrk
    have hcV : Nat.card (LinearMap.ker H) = 2 ^ (n - Fintype.card ι) := by
      haveI := Fintype.ofFinite (LinearMap.ker H)
      rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
      congr 1; omega
    rw [hcV, ← pow_add]; congr 1; omega

/-- U5: `r` blocks of the Hamming parity check of length `2^m - 1`. -/
lemma g40u_block (r m : ℕ) : ∃ H : 𝔽₂ (r * (2 ^ m - 1)) →ₗ[ZMod 2] (Fin r × Fin m → ZMod 2),
    ∀ s, ∃ y, hammingNorm y ≤ r ∧ H y = s := by
  classical
  set n' := 2 ^ m - 1 with hn'
  have hcard : Fintype.card {v : Fin m → ZMod 2 // v ≠ 0} = n' := by
    rw [Fintype.card_subtype_compl, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    simp [hn']
  let e : Fin n' ≃ {v : Fin m → ZMod 2 // v ≠ 0} := (Fintype.equivFinOfCardEq hcard).symm
  let φ : Fin r × Fin n' ≃ Fin (r * n') := finProdFinEquiv
  let H : 𝔽₂ (r * n') →ₗ[ZMod 2] (Fin r × Fin m → ZMod 2) :=
    LinearMap.pi (fun p : Fin r × Fin m =>
      ∑ i : Fin n', ((e i).1 p.2) • LinearMap.proj (R := ZMod 2) (φ (p.1, i)))
  have hH : ∀ x p, H x p = ∑ i : Fin n', (e i).1 p.2 * x (φ (p.1, i)) := by
    intro x p; simp [H]
  refine ⟨H, fun s => ?_⟩
  let sb : Fin r → (Fin m → ZMod 2) := fun k j => s (k, j)
  let y : 𝔽₂ (r * n') := fun idx =>
    if h : sb (φ.symm idx).1 = 0 then 0
    else if (φ.symm idx).2 = e.symm ⟨sb (φ.symm idx).1, h⟩ then 1 else 0
  refine ⟨y, ?_, ?_⟩
  · unfold hammingNorm
    calc (Finset.univ.filter (fun idx => y idx ≠ 0)).card ≤ (Finset.univ : Finset (Fin r)).card := by
          apply Finset.card_le_card_of_injOn (fun idx => (φ.symm idx).1)
          · intro _ _; simp
          · intro a ha b hb hab
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha hb
            simp only at hab
            have key : ∀ c, y c ≠ 0 → ∃ h : sb (φ.symm c).1 ≠ 0,
                (φ.symm c).2 = e.symm ⟨sb (φ.symm c).1, h⟩ := by
              intro c hc
              simp only [y] at hc
              split_ifs at hc with h1 h2
              · exact absurd rfl hc
              · exact ⟨h1, h2⟩
              · exact absurd rfl hc
            obtain ⟨ha1, ha2⟩ := key a ha
            obtain ⟨hb1, hb2⟩ := key b hb
            apply φ.symm.injective
            ext1
            · exact hab
            · rw [ha2, hb2]; congr 2; rw [hab]
      _ = r := by simp
  · funext ⟨k, j⟩
    rw [hH]
    simp only [y, Equiv.symm_apply_apply]
    by_cases hk : sb k = 0
    · simp only [hk, dite_true, mul_zero, Finset.sum_const_zero]
      exact (congrFun hk j).symm
    · simp only [hk, dite_false, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_eq_single (e.symm ⟨sb k, hk⟩)]
      · rw [if_pos rfl, Equiv.apply_symm_apply]
      · intro b _ hb; rw [if_neg hb]
      · intro h; exact absurd (Finset.mem_univ _) h

lemma g40u_density (n r : ℕ) {ι : Type} [Fintype ι] (H : 𝔽₂ n →ₗ[ZMod 2] (ι → ZMod 2))
    (hH : ∀ s, ∃ y, hammingNorm y ≤ r ∧ H y = s) (hk : (n + r) ^ r ≤ r ^ r * 2 ^ Fintype.card ι) :
    minDensity n r ≤ (r ^ r : ℝ≥0∞) / (r.factorial : ℝ≥0∞) := by
  obtain ⟨hcov, hcard⟩ := g40u_gen n r H hH
  unfold minDensity
  refine (iInf₂_le _ hcov).trans ?_
  set cV := Nat.card (LinearMap.ker H)
  set cB := Nat.card (hammingBall n r)
  have hB : cB * r.factorial ≤ (n + r) ^ r :=
    le_trans (Nat.mul_le_mul_right _ ((g40u_card_ball_le n r).trans (g40u_sum_choose_le n r)))
      (g40u_choose_fact _ _)
  have hnat : cV * cB * r.factorial ≤ r ^ r * 2 ^ n := by
    calc cV * cB * r.factorial = cV * (cB * r.factorial) := by ring
      _ ≤ cV * (r ^ r * 2 ^ Fintype.card ι) := Nat.mul_le_mul_left _ (hB.trans hk)
      _ = r ^ r * (cV * 2 ^ Fintype.card ι) := by ring
      _ = r ^ r * 2 ^ n := by rw [hcard]
  rw [ENNReal.div_le_iff_le_mul (Or.inl (by simp)) (Or.inl (by simp))]
  rw [show (r ^ r : ℝ≥0∞) / (r.factorial : ℝ≥0∞) * 2 ^ n = (r ^ r * 2 ^ n) / (r.factorial : ℝ≥0∞) by
    rw [div_eq_mul_inv, div_eq_mul_inv]; ring]
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simp [Nat.factorial_ne_zero])) (Or.inl (by simp))]
  exact_mod_cast hnat

theorem g40u_main (r : ℕ) : f r ≤ (r ^ r : ℝ≥0∞) / (r.factorial : ℝ≥0∞) := by
  unfold f
  apply Filter.liminf_le_of_frequently_le'
  rw [Filter.frequently_atTop]
  intro a
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · refine ⟨a, le_rfl, ?_⟩
    have := g40u_density a 0 (ι := Fin 0) 0 (fun s => ⟨0, by simp, by funext i; exact i.elim0⟩)
      (by simp)
    simpa using this
  · obtain ⟨H, hH⟩ := g40u_block r (a + 1)
    refine ⟨r * (2 ^ (a + 1) - 1), ?_, g40u_density _ r H hH ?_⟩
    · have := Nat.lt_two_pow_self (n := a + 1)
      calc a ≤ 2 ^ (a + 1) - 1 := by omega
        _ ≤ r * (2 ^ (a + 1) - 1) := Nat.le_mul_of_pos_left _ hr
    · have h1 : r * (2 ^ (a + 1) - 1) + r = r * 2 ^ (a + 1) := by
        have := Nat.one_le_two_pow (n := a + 1)
        rw [← Nat.mul_add_one, Nat.sub_add_cancel this]
      rw [h1, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, mul_pow, ← pow_mul, mul_comm (a + 1)]

/-- $f(r) \le r^r / r! \sim e^r$ [Gr24]. -/
@[category research solved, AMS 5 94]
theorem green_40.upper_bound (r : ℕ) : f r ≤ (r ^ r : ℝ≥0∞) / (r.factorial : ℝ≥0∞) := by
  exact g40u_main r

/-- The possibility that f(r) = 1 for all r has not been ruled out [Gr24] -/
@[category research open, AMS 5 94]
theorem green_40.f_eq_one_for_all : answer(sorry) ↔ ∀ r, f r = 1 := by
  sorry

/-- It is not known whether f(2) = 1 [Gr24] -/
@[category research open, AMS 5 94]
theorem green_40.f_two_eq_one : answer(sorry) ↔ f 2 = 1 := by
  sorry

/-- The best-known upper bound for $f(2)$ is $1.4238$ [CHL97]. -/
@[category research solved, AMS 5 94]
theorem green_40.upper_bound_f_two : f 2 ≤ (1.4238 : ℝ≥0∞) := by
  sorry

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- Variant with arbitrary subsets
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

def hammingBallFinset (n r : ℕ) : Finset (𝔽₂ n) :=
  Finset.univ.filter (fun x => hammingNorm x ≤ r)

def IsCoveringFinset (n r : ℕ) (V : Finset (𝔽₂ n)) : Prop :=
  V + hammingBallFinset n r = Finset.univ

noncomputable def minDensityFinset (n r : ℕ) : ℝ≥0∞ :=
  ⨅ (V : Finset (𝔽₂ n)) (_ : IsCoveringFinset n r V),
    (V.card : ℝ≥0∞) * (Nat.card (hammingBall n r) : ℝ≥0∞) / (2 ^ n : ℝ≥0∞)

noncomputable def f_tilde (r : ℕ) : ℝ≥0∞ :=
  liminf (fun n ↦ minDensityFinset n r) atTop

/-- Does $\tilde{f}(r) \to \infty$? [Gr24] -/
@[category research open, AMS 5 94]
theorem green_40.variants.arbitrary_subsets : answer(sorry) ↔ Tendsto f_tilde atTop (𝓝 ⊤) := by
  sorry

/-- It is known that $\tilde{f}(2) = 1$ [St94]. -/
@[category research solved, AMS 5 94]
theorem green_40.variants.arbitrary_subsets_sanity_f_tilde_two : f_tilde 2 = 1 := by
  sorry

/-- We evidently have $\tilde{f}(r) \le f(r)$ [Gr24]. -/
@[category research solved, AMS 5 94]
theorem green_40.f_tilde_le_f (r : ℕ) : f_tilde r ≤ f r := by
  refine Filter.liminf_le_liminf (Filter.Eventually.of_forall fun n => ?_)
  refine le_iInf₂ fun V hV => ?_
  have hfin : (V : Set (𝔽₂ n)).Finite := Set.toFinite _
  have hcov : IsCoveringFinset n r hfin.toFinset := by
    unfold IsCoveringFinset
    ext x
    simp only [Finset.mem_univ, iff_true]
    have hx : x ∈ (V : Set (𝔽₂ n)) + hammingBall n r := hV ▸ Set.mem_univ x
    obtain ⟨a, ha, b, hb, hab⟩ := hx
    exact Finset.mem_add.mpr
      ⟨a, hfin.mem_toFinset.mpr ha, b, by simpa [hammingBallFinset, hammingBall] using hb, hab⟩
  have hcard : (hfin.toFinset.card : ℝ≥0∞) = (Nat.card V : ℝ≥0∞) := by
    have h : Nat.card V = hfin.toFinset.card := by
      rw [show Nat.card V = Nat.card (V : Set (𝔽₂ n)) from rfl, Nat.card_coe_set_eq,
        Set.ncard_eq_toFinset_card _ hfin]
    exact_mod_cast congrArg Nat.cast h.symm
  calc minDensityFinset n r
      ≤ (hfin.toFinset.card : ℝ≥0∞) * (Nat.card (hammingBall n r) : ℝ≥0∞) /
          (2 ^ n : ℝ≥0∞) :=
        iInf₂_le hfin.toFinset hcov
    _ = (Nat.card V : ℝ≥0∞) * (Nat.card (hammingBall n r) : ℝ≥0∞) /
          (2 ^ n : ℝ≥0∞) := by
        rw [hcard]

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- Variant for all n
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

noncomputable def f_all (r : ℕ) : ℝ≥0∞ :=
  limsup (fun n ↦ minDensity n r) atTop

/-- Does $f_{\text{all}}(r) \to \infty$? [Gr24]

The target filter is `𝓝 ⊤`, as in `green_40` and `green_40.variants.arbitrary_subsets`. On
`ℝ≥0∞`, `atTop` is the principal ultrafilter at `⊤`, so `Tendsto f_all atTop atTop` would say
that `f_all r = ⊤` for all large `r` rather than that `f_all r → ∞`. -/
@[category research open, AMS 5 94]
theorem green_40.variants.all_n : answer(sorry) ↔ Tendsto f_all atTop (𝓝 ⊤) := by
  sorry

end Green40
