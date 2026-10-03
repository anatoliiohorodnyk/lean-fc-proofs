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
# Erdős Problem 102

*Reference:* [erdosproblems.com/102](https://www.erdosproblems.com/102)
-/

@[expose] public section

namespace Erdos102

open EuclideanGeometry Filter

open scoped Classical in
/-- The number of points of `P` that lie on `L`. -/
noncomputable def pointsOn (P : Finset ℝ²) (L : AffineSubspace ℝ ℝ²) : ℕ :=
  (P.filter (· ∈ L)).card

/-- The number of lines that contain more than three points of `P`. -/
noncomputable def richLineCount (P : Finset ℝ²) : ℕ :=
  {L : AffineSubspace ℝ ℝ² | IsLine L ∧ 3 < pointsOn P L}.ncard

/-- `P` has $n$ points and at least $c n^2$ lines that each contain more than three points
of `P`. -/
def Admissible (c : ℝ) (n : ℕ) (P : Finset ℝ²) : Prop :=
  P.card = n ∧ c * (n : ℝ) ^ 2 ≤ richLineCount P

/-- The largest number of points of `P` on a single line. -/
noncomputable def maxCollinear (P : Finset ℝ²) : ℕ :=
  sSup {k : ℕ | ∃ L, IsLine L ∧ pointsOn P L = k}

/-- $h_c(n)$: the minimum of `maxCollinear P` over all admissible `P`. It is `⊤` when no
admissible configuration exists.

Two distinct lines share at most one pair of points, and a line with more than three points of
`P` contains at least $\binom{4}{2} = 6$ pairs. Hence `richLineCount P` $< n^2 / 12$, so for
$c \geq 1/12$ and $n \geq 1$ no configuration is admissible and $h_c(n) = \top$. The problem is
only meaningful for small $c > 0$; the statements below either quantify over all $c > 0$ (where
small $c$ govern the truth value) or restrict to sufficiently small $c$. -/
noncomputable def h (c : ℝ) (n : ℕ) : ℕ∞ :=
  ⨅ (P : Finset ℝ²) (_ : Admissible c n P), (maxCollinear P : ℕ∞)

/-- The plane contains a line. -/
@[category API, AMS 52]
theorem exists_line : ∃ L : AffineSubspace ℝ ℝ², IsLine L := by
  refine ⟨AffineSubspace.mk' 0 (Submodule.span ℝ {EuclideanSpace.single 0 1}), ?_⟩
  unfold IsLine
  rw [AffineSubspace.direction_mk']
  apply finrank_span_singleton
  simp

/-- `M ≤ maxCollinear P` exactly when some line contains at least `M` points of `P`. -/
@[category API, AMS 52]
theorem le_maxCollinear_iff (P : Finset ℝ²) (M : ℕ) :
    M ≤ maxCollinear P ↔ ∃ L, IsLine L ∧ M ≤ pointsOn P L := by
  have hbdd : BddAbove {k : ℕ | ∃ L, IsLine L ∧ pointsOn P L = k} := by
    refine ⟨P.card, ?_⟩
    rintro k ⟨L, -, rfl⟩
    classical
    exact Finset.card_filter_le _ _
  have hne : {k : ℕ | ∃ L, IsLine L ∧ pointsOn P L = k}.Nonempty := by
    obtain ⟨L, hL⟩ := exists_line
    exact ⟨_, L, hL, rfl⟩
  constructor
  · intro hM
    obtain ⟨L, hL, hk⟩ := Nat.sSup_mem hne hbdd
    exact ⟨L, hL, hk ▸ hM⟩
  · rintro ⟨L, hL, hM⟩
    exact hM.trans (le_csSup hbdd ⟨L, hL, rfl⟩)

/-- `M ≤ h c n` exactly when every admissible configuration of $n$ points has a line that
contains at least `M` of its points. -/
@[category API, AMS 52]
theorem le_h_iff (c : ℝ) (n M : ℕ) :
    (M : ℕ∞) ≤ h c n ↔
      ∀ P : Finset ℝ², Admissible c n P → ∃ L, IsLine L ∧ M ≤ pointsOn P L := by
  simp only [h, le_iInf_iff, Nat.cast_le]
  refine forall_congr' fun P => imp_congr_right fun _ => ?_
  exact le_maxCollinear_iff P M

/-- The statement $h_c(n) \to \infty$, written without $h_c$. -/
@[category API, AMS 52]
theorem tendsto_h_iff (c : ℝ) :
    (∀ M : ℕ, ∀ᶠ n in atTop, (M : ℕ∞) ≤ h c n) ↔
      ∀ M : ℕ, ∀ᶠ n in atTop, ∀ P : Finset ℝ², P.card = n →
        c * (n : ℝ) ^ 2 ≤ richLineCount P → ∃ L, IsLine L ∧ M ≤ pointsOn P L := by
  refine forall_congr' fun M => eventually_congr (Eventually.of_forall fun n => ?_)
  rw [le_h_iff]
  exact forall_congr' fun P => ⟨fun hP hcard hrich => hP ⟨hcard, hrich⟩,
    fun hP hadm => hP hadm.1 hadm.2⟩


/-- 2×2 determinant in the plane. -/
noncomputable def e102det (a b : ℝ²) : ℝ := a 0 * b 1 - a 1 * b 0

/-- B1: three points of a line have vanishing determinant. -/
lemma e102_B1 (L : AffineSubspace ℝ ℝ²) (hL : IsLine L) (p q r : ℝ²) (hp : p ∈ L) (hq : q ∈ L)
    (hr : r ∈ L) : e102det (q - p) (r - p) = 0 := by
  have hq' : q -ᵥ p ∈ L.direction := AffineSubspace.vsub_mem_direction hq hp
  have hr' : r -ᵥ p ∈ L.direction := AffineSubspace.vsub_mem_direction hr hp
  by_cases h0 : q -ᵥ p = 0
  · have : q - p = 0 := h0
    simp [e102det, this]
  · have hne : (⟨q -ᵥ p, hq'⟩ : L.direction) ≠ 0 := by
      intro h; apply h0; simpa using congrArg Subtype.val h
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp hL ⟨r -ᵥ p, hr'⟩
    have hc' : c • (q - p) = r - p := by simpa using congrArg Subtype.val hc
    rw [← hc']
    simp only [e102det, PiLp.smul_apply, smul_eq_mul]
    ring

/-- Integer vectors `u, w` are parallel. -/
def e102Par {d : ℕ} (u w : Fin d → ℤ) : Prop := ∀ i j, u i * w j = u j * w i

/-- B2: a set of grid points whose differences from a base point are all parallel to a fixed
nonzero difference has at most `m` elements. -/
lemma e102_B2 {d : ℕ} (m : ℕ) (hm : 1 ≤ m) (S : Finset (Fin d → ℤ))
    (hG : ∀ x ∈ S, ∀ i, 1 ≤ x i ∧ x i ≤ m)
    (hpar : ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, e102Par (q - p) (r - p)) : S.card ≤ m := by
  classical
  by_cases hS : ∃ p ∈ S, ∃ q ∈ S, p ≠ q
  · obtain ⟨p, hp, q, hq, hpq⟩ := hS
    obtain ⟨i, hi⟩ : ∃ i, (q - p) i ≠ 0 := by
      by_contra h; push Not at h; exact hpq (funext fun j => by have := h j; simp at this; omega)
    calc S.card ≤ (Finset.Icc (1 : ℤ) m).card := by
          apply Finset.card_le_card_of_injOn (fun r => r i)
          · intro r hr; simp only [Finset.coe_Icc, Set.mem_Icc]; exact hG r hr i
          · intro r hr r' hr' hrr
            simp only at hrr
            funext j
            have h1 := hpar p hp q hq r hr i j
            have h2 := hpar p hp q hq r' hr' i j
            simp only [Pi.sub_apply] at h1 h2 hi
            have : (r j - p j) * (q i - p i) = (r' j - p j) * (q i - p i) := by
              rw [hrr] at h1; linarith
            have := mul_right_cancel₀ hi this
            linarith
      _ = m := by simp
  · push Not at hS
    have : S.card ≤ 1 := Finset.card_le_one.mpr (fun a ha b hb => hS a ha b hb)
    omega

/-- The grid `[1, m]^d`. -/
noncomputable def e102G (d m : ℕ) : Finset (Fin d → ℤ) := Fintype.piFinset (fun _ => Finset.Icc (1 : ℤ) m)

lemma e102_memG {d m : ℕ} {x : Fin d → ℤ} : x ∈ e102G d m ↔ ∀ i, 1 ≤ x i ∧ x i ≤ m := by
  simp [e102G, Fintype.mem_piFinset]

/-- `φ` is collinearity-faithful at scale `m`. -/
def e102Faithful {d : ℕ} (φ : (Fin d → ℤ) →+ ℝ²) (m : ℕ) : Prop :=
  ∀ u w : Fin d → ℤ, (∀ i, |u i| < m) → (∀ i, |w i| < m) →
    e102det (φ u) (φ w) = 0 → e102Par u w

open scoped Classical in
/-- B3: every line contains at most `m` points of `φ(G)`. -/
lemma e102_B3 {d : ℕ} (m : ℕ) (hm : 1 ≤ m) (φ : (Fin d → ℤ) →+ ℝ²) (hφ : e102Faithful φ m)
    (L : AffineSubspace ℝ ℝ²) (hL : IsLine L) :
    (((e102G d m).image φ).filter (· ∈ L)).card ≤ m := by
  have hsub : ((e102G d m).image φ).filter (· ∈ L) ⊆ ((e102G d m).filter (fun x => φ x ∈ L)).image φ := by
    intro y hy
    rw [Finset.mem_filter, Finset.mem_image] at hy
    obtain ⟨⟨x, hx, rfl⟩, hyL⟩ := hy
    exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hyL⟩, rfl⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  apply e102_B2 m hm
  · intro x hx; exact e102_memG.mp (Finset.mem_filter.mp hx).1
  · intro p hp q hq r hr
    obtain ⟨hpG, hpL⟩ := Finset.mem_filter.mp hp
    obtain ⟨hqG, hqL⟩ := Finset.mem_filter.mp hq
    obtain ⟨hrG, hrL⟩ := Finset.mem_filter.mp hr
    have hdet := e102_B1 L hL (φ p) (φ q) (φ r) hpL hqL hrL
    rw [← map_sub, ← map_sub] at hdet
    have hb : ∀ a ∈ e102G d m, ∀ b ∈ e102G d m, ∀ i, |(a - b) i| < m := by
      intro a ha b hb i
      have h1 := e102_memG.mp ha i; have h2 := e102_memG.mp hb i
      simp only [Pi.sub_apply]; rw [abs_lt]; constructor <;> omega
    exact hφ _ _ (hb q hqG p hpG) (hb r hrG p hpG) hdet

/-- det is additive in the second argument. -/
lemma e102_det_add (a b c : ℝ²) : e102det a (b + c) = e102det a b + e102det a c := by
  simp only [e102det, PiLp.add_apply]; ring

lemma e102_det_self (a : ℝ²) : e102det a a = 0 := by simp only [e102det]; ring

lemma e102_det_swap (a b : ℝ²) : e102det a b = - e102det b a := by simp only [e102det]; ring

/-- C1: if `gcd(v₀, v₁) = 1` then every integer vector parallel to `v` is an integer multiple. -/
lemma e102_C1 {d : ℕ} (hd : 2 ≤ d) (v w : Fin d → ℤ)
    (hv : Int.gcd (v ⟨0, by omega⟩) (v ⟨1, by omega⟩) = 1) (hpar : e102Par w v) :
    ∃ k : ℤ, w = k • v := by
  set i0 : Fin d := ⟨0, by omega⟩
  set i1 : Fin d := ⟨1, by omega⟩
  have hbez := Int.gcd_eq_gcd_ab (v i0) (v i1)
  rw [hv] at hbez
  refine ⟨w i0 * Int.gcdA (v i0) (v i1) + w i1 * Int.gcdB (v i0) (v i1), funext fun j => ?_⟩
  have h0 := hpar i0 j
  have h1 := hpar i1 j
  simp only [Pi.smul_apply, smul_eq_mul]
  have : w j = w j * (v i0 * Int.gcdA (v i0) (v i1) + v i1 * Int.gcdB (v i0) (v i1)) := by
    rw [← hbez]; push_cast; ring
  rw [this]
  linear_combination (-(Int.gcdA (v i0) (v i1))) * h0 + (-(Int.gcdB (v i0) (v i1))) * h1

/-- The plane line through `φ x` in direction `φ v`. -/
noncomputable def e102line {d : ℕ} (φ : (Fin d → ℤ) →+ ℝ²) (x v : Fin d → ℤ) :
    AffineSubspace ℝ ℝ² :=
  AffineSubspace.mk' (φ x) (Submodule.span ℝ {φ v})

lemma e102_line_isLine {d : ℕ} (φ : (Fin d → ℤ) →+ ℝ²) (x v : Fin d → ℤ) (hv : φ v ≠ 0) :
    IsLine (e102line φ x v) := by
  unfold IsLine e102line
  rw [AffineSubspace.direction_mk']
  exact finrank_span_singleton hv

lemma e102_mem_line {d : ℕ} (φ : (Fin d → ℤ) →+ ℝ²) (x v : Fin d → ℤ) (k : ℤ) :
    φ (x + k • v) ∈ e102line φ x v := by
  unfold e102line
  rw [AffineSubspace.mem_mk', map_add, map_zsmul]
  rw [show (φ x + k • φ v) -ᵥ φ x = k • φ v by simp [vsub_eq_sub]]
  exact Submodule.smul_of_tower_mem _ k (Submodule.mem_span_singleton_self _)

lemma e102_det_smul (a : ℝ²) (c : ℝ) : e102det (c • a) a = 0 := by
  simp only [e102det, PiLp.smul_apply, smul_eq_mul]; ring

/-- C3a: equal lines have parallel directions and parallel start difference. -/
lemma e102_line_eq {d : ℕ} (φ : (Fin d → ℤ) →+ ℝ²) (x v x' v' : Fin d → ℤ)
    (h : e102line φ x v = e102line φ x' v') :
    e102det (φ v') (φ v) = 0 ∧ e102det (φ (x' - x)) (φ v) = 0 := by
  have hdir : Submodule.span ℝ {φ v} = Submodule.span ℝ {φ v'} := by
    have := congrArg AffineSubspace.direction h
    simpa [e102line, AffineSubspace.direction_mk'] using this
  constructor
  · have : φ v' ∈ Submodule.span ℝ {φ v} := hdir ▸ Submodule.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp this
    rw [← hc]; exact e102_det_smul _ c
  · have hx' : φ x' ∈ e102line φ x v := by
      rw [h]; simpa using e102_mem_line φ x' v' 0
    unfold e102line at hx'
    rw [AffineSubspace.mem_mk'] at hx'
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx'
    rw [map_sub, show φ x' - φ x = φ x' -ᵥ φ x from rfl, ← hc]
    exact e102_det_smul _ c

/-- Good directions: coordinates in `[1, K]`, first coordinate `> K/2`, first two coprime. -/
def e102GoodDir {d : ℕ} (hd : 2 ≤ d) (K : ℕ) (v : Fin d → ℤ) : Prop :=
  (∀ i, 1 ≤ v i ∧ v i ≤ K) ∧ Int.gcd (v ⟨0, by omega⟩) (v ⟨1, by omega⟩) = 1

/-- Starts for direction `v`: `x₀ ∈ [1, v₀]`, other coordinates in `[1, R]`. -/
def e102Start {d : ℕ} (hd : 2 ≤ d) (R : ℕ) (v x : Fin d → ℤ) : Prop :=
  (1 ≤ x ⟨0, by omega⟩ ∧ x ⟨0, by omega⟩ ≤ v ⟨0, by omega⟩) ∧ ∀ i, 1 ≤ x i ∧ x i ≤ R

/-- C3: the lines indexed by (good direction, start) are pairwise distinct. -/
lemma e102_C3 {d : ℕ} (hd : 2 ≤ d) (m K R : ℕ) (hK : K < m) (hR : R ≤ m)
    (φ : (Fin d → ℤ) →+ ℝ²) (hφ : e102Faithful φ m)
    (v x v' x' : Fin d → ℤ) (hv : e102GoodDir hd K v) (hv' : e102GoodDir hd K v')
    (hx : e102Start hd R v x) (hx' : e102Start hd R v' x')
    (h : e102line φ x v = e102line φ x' v') : v = v' ∧ x = x' := by
  obtain ⟨h1, h2⟩ := e102_line_eq φ x v x' v' h
  set i0 : Fin d := ⟨0, by omega⟩
  have hsmall : ∀ u : Fin d → ℤ, (∀ i, 1 ≤ u i ∧ u i ≤ m) → ∀ w : Fin d → ℤ,
      (∀ i, 1 ≤ w i ∧ w i ≤ m) → ∀ i, |(u - w) i| < m := by
    intro u hu w hw i
    have := hu i; have := hw i
    simp only [Pi.sub_apply]; rw [abs_lt]; constructor <;> omega
  have hvsm : ∀ u : Fin d → ℤ, e102GoodDir hd K u → ∀ i, |u i| < m := by
    intro u hu i
    have := hu.1 i; rw [abs_lt]; constructor <;> omega
  -- directions
  have hpar1 : e102Par v' v := hφ v' v (hvsm v' hv') (hvsm v hv) h1
  have hpar2 : e102Par v v' := fun i j => by
    linarith [hpar1 i j, mul_comm (v i) (v' j), mul_comm (v j) (v' i)]
  obtain ⟨k, hk⟩ := e102_C1 hd v v' hv.2 hpar1
  obtain ⟨k', hk'⟩ := e102_C1 hd v' v hv'.2 hpar2
  have hv0 := (hv.1 i0).1
  have hv'0 := (hv'.1 i0).1
  have hk0 : v' i0 = k * v i0 := by rw [hk]; rfl
  have hk'0 : v i0 = k' * v' i0 := by rw [hk']; rfl
  have hkk : k * k' = 1 := by
    have : v i0 = (k' * k) * v i0 := by rw [mul_assoc, ← hk0, ← hk'0]
    have : (k' * k - 1) * v i0 = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · omega
  have hk1 : k = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hkk with h | h
    · exact h
    · rw [h] at hk0; omega
  have hvv : v = v' := by rw [hk, hk1, one_smul]
  refine ⟨hvv, ?_⟩
  -- starts
  have hxs : ∀ u : Fin d → ℤ, e102Start hd R v u → ∀ i, 1 ≤ u i ∧ u i ≤ m := by
    intro u hu i; have := hu.2 i; constructor <;> omega
  have hx'v : e102Start hd R v x' := by rw [hvv]; exact hx'
  have hpar3 : e102Par (x' - x) v := hφ _ _ (hsmall x' (hxs x' hx'v) x (hxs x hx)) (hvsm v hv) h2
  obtain ⟨j, hj⟩ := e102_C1 hd v (x' - x) hv.2 hpar3
  have hj0 : x' i0 - x i0 = j * v i0 := by
    have := congrFun hj i0; simpa using this
  have hjz : j = 0 := by
    have ha : 1 ≤ x i0 ∧ x i0 ≤ v i0 := hx.1
    have hb : 1 ≤ x' i0 ∧ x' i0 ≤ v i0 := hx'v.1
    by_contra hne
    rcases lt_or_gt_of_ne hne with hl | hl
    · have : j * v i0 ≤ - v i0 := by nlinarith
      generalize j * v i0 = J at *
      omega
    · have : v i0 ≤ j * v i0 := by nlinarith
      generalize j * v i0 = J at *
      omega
  rw [hjz, zero_smul, sub_eq_zero] at hj
  exact hj.symm

open scoped Classical in
/-- C4: a line through `x` in a good direction contains at least 4 points of `φ(G)`. -/
lemma e102_C4 {d : ℕ} (hd : 2 ≤ d) (m K R : ℕ) (hKR : R + 3 * K ≤ m)
    (φ : (Fin d → ℤ) →+ ℝ²)
    (hinj : ∀ a ∈ e102G d m, ∀ b ∈ e102G d m, φ a = φ b → a = b)
    (v x : Fin d → ℤ) (hv : e102GoodDir hd K v) (hx : e102Start hd R v x) :
    3 < (((e102G d m).image φ).filter (· ∈ e102line φ x v)).card := by
  set i0 : Fin d := ⟨0, by omega⟩
  have hmem : ∀ k : ℕ, k < 4 → x + (k : ℤ) • v ∈ e102G d m := by
    intro k hk
    rw [e102_memG]
    intro i
    have h1 := hv.1 i; have h2 := hx.2 i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have : (k : ℤ) ≤ 3 := by exact_mod_cast (by omega : k ≤ 3)
    constructor <;> nlinarith
  have hsub : (Finset.range 4).image (fun k : ℕ => φ (x + (k : ℤ) • v)) ⊆
      ((e102G d m).image φ).filter (· ∈ e102line φ x v) := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
    rw [Finset.mem_range] at hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨_, hmem k hk, rfl⟩, e102_mem_line φ x v k⟩
  have hcard : ((Finset.range 4).image (fun k : ℕ => φ (x + (k : ℤ) • v))).card = 4 := by
    rw [Finset.card_image_of_injOn]
    · simp
    · intro k hk k' hk' h
      simp only [Finset.coe_range, Set.mem_Iio] at hk hk'
      have := hinj _ (hmem k hk) _ (hmem k' hk') h
      have h0 := congrFun this i0
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_right_inj] at h0
      have hv0 := (hv.1 i0).1
      have : (k : ℤ) = k' := mul_right_cancel₀ (by omega) h0
      exact_mod_cast this
  have := Finset.card_le_card hsub
  omega

/-- A line containing two distinct points is their affine span. -/
lemma e102_line_eq_span (L : AffineSubspace ℝ ℝ²) (hL : IsLine L) (p q : ℝ²) (hp : p ∈ L)
    (hq : q ∈ L) (hpq : p ≠ q) : L = affineSpan ℝ {p, q} := by
  symm
  apply AffineSubspace.eq_of_direction_eq_of_nonempty_of_le
  · rw [direction_affineSpan, vectorSpan_pair]
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_singleton_le_iff_mem]
      exact AffineSubspace.vsub_mem_direction hp hq
    · rw [finrank_span_singleton (vsub_ne_zero.mpr hpq)]; exact hL.symm
  · exact ⟨p, subset_affineSpan ℝ _ (Set.mem_insert _ _)⟩
  · rw [affineSpan_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact hp
    · exact hq

open scoped Classical in
/-- F: the set of lines with more than three points of a finite set is finite. -/
lemma e102_rich_finite (P : Finset ℝ²) :
    {L : AffineSubspace ℝ ℝ² | IsLine L ∧ 3 < (P.filter (· ∈ L)).card}.Finite := by
  apply ((P ×ˢ P).image (fun pq => affineSpan ℝ {pq.1, pq.2})).finite_toSet.subset
  intro L ⟨hL, h3⟩
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < (P.filter (· ∈ L)).card)
  rw [Finset.mem_filter] at hp hq
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product]
  exact ⟨(p, q), ⟨hp.1, hq.1⟩, (e102_line_eq_span L hL p q hp.2 hq.2 hpq).symm⟩

/-- `φ v ≠ 0` for good directions (faithfulness against `e₀`). -/
lemma e102_phi_ne {d : ℕ} (hd : 2 ≤ d) (m K : ℕ) (hm : 2 ≤ m) (hK : K < m)
    (φ : (Fin d → ℤ) →+ ℝ²) (hφ : e102Faithful φ m) (v : Fin d → ℤ) (hv : e102GoodDir hd K v) :
    φ v ≠ 0 := by
  intro h0
  set i0 : Fin d := ⟨0, by omega⟩
  set i1 : Fin d := ⟨1, by omega⟩
  let e : Fin d → ℤ := fun i => if i = i0 then 1 else 0
  have hpar := hφ v e (fun i => by have := hv.1 i; rw [abs_lt]; constructor <;> omega)
    (fun i => by simp only [e]; split_ifs <;> simp <;> omega) (by simp [e102det, h0])
  have := hpar i1 i0
  have hne : i1 ≠ i0 := by simp [i0, i1, Fin.ext_iff]
  simp only [e, if_pos rfl, if_neg hne, mul_one, mul_zero] at this
  have := (hv.1 i1).1
  omega

open scoped Classical in
/-- C5: rich lines are at least as many as admissible (direction, start) pairs. -/
lemma e102_C5 {d : ℕ} (hd : 2 ≤ d) (m K R : ℕ) (hm : 2 ≤ m) (hKm : K < m) (hRm : R ≤ m)
    (hKR : R + 3 * K ≤ m) (φ : (Fin d → ℤ) →+ ℝ²) (hφ : e102Faithful φ m)
    (hinj : ∀ a ∈ e102G d m, ∀ b ∈ e102G d m, φ a = φ b → a = b)
    (I : Finset ((Fin d → ℤ) × (Fin d → ℤ)))
    (hI : ∀ p ∈ I, e102GoodDir hd K p.1 ∧ e102Start hd R p.1 p.2) :
    I.card ≤ {L : AffineSubspace ℝ ℝ² |
      IsLine L ∧ 3 < (((e102G d m).image φ).filter (· ∈ L)).card}.ncard := by
  have hinjI : Set.InjOn (fun p : (Fin d → ℤ) × (Fin d → ℤ) => e102line φ p.2 p.1) I := by
    intro p hp p' hp' h
    obtain ⟨hv, hx⟩ := hI p hp
    obtain ⟨hv', hx'⟩ := hI p' hp'
    obtain ⟨h1, h2⟩ := e102_C3 hd m K R hKm hRm φ hφ p.1 p.2 p'.1 p'.2 hv hv' hx hx' h
    exact Prod.ext h1 h2
  rw [← Finset.card_image_of_injOn hinjI, ← Set.ncard_coe_finset]
  apply Set.ncard_le_ncard _ (e102_rich_finite _)
  intro L hL
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hL
  obtain ⟨p, hp, rfl⟩ := hL
  obtain ⟨hv, hx⟩ := hI p hp
  exact ⟨e102_line_isLine φ p.2 p.1 (e102_phi_ne hd m K hm hKm φ hφ p.1 hv),
    e102_C4 hd m K R hKR φ hinj p.1 p.2 hv hx⟩

/-- Multiples of `g` in `(a, b]`. -/
lemma e102_mult_Ioc (a b g : ℕ) (hg : 1 ≤ g) :
    ((Finset.Ioc a b).filter (g ∣ ·)).card ≤ (b - a) / g + 2 := by
  calc ((Finset.Ioc a b).filter (g ∣ ·)).card ≤ (Finset.Icc (a / g) (b / g)).card := by
        apply Finset.card_le_card_of_injOn (fun x => x / g)
        · intro x hx
          simp only [Finset.coe_filter, Finset.mem_Ioc, Set.mem_setOf_eq] at hx
          simp only [Finset.coe_Icc, Set.mem_Icc]
          exact ⟨Nat.div_le_div_right (by omega), Nat.div_le_div_right hx.1.2⟩
        · intro x hx y hy h
          simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
          simp only at h
          rw [← Nat.div_mul_cancel hx.2, ← Nat.div_mul_cancel hy.2, h]
    _ = b / g + 1 - a / g := by simp
    _ ≤ (b - a) / g + 2 := by
        have : b / g ≤ (b - a) / g + a / g + 1 := by
          rcases le_total a b with hab | hab
          · have hb : b = (b - a) + a := by omega
            have := Nat.add_div (a := b - a) (b := a) (by omega : 0 < g)
            rw [← hb] at this
            generalize (b - a) / g = X at *
            generalize a / g = Y at *
            generalize b / g = Z at *
            split_ifs at this <;> omega
          · have : b / g ≤ a / g := Nat.div_le_div_right hab
            generalize (b - a) / g = X at *
            generalize a / g = Y at *
            generalize b / g = Z at *
            omega
        generalize (b - a) / g = X at *
        generalize a / g = Y at *
        generalize b / g = Z at *
        omega

/-- Multiples of `g` in `[1, K]`. -/
lemma e102_mult_Icc (K g : ℕ) (hg : 1 ≤ g) : ((Finset.Icc 1 K).filter (g ∣ ·)).card ≤ K / g := by
  calc ((Finset.Icc 1 K).filter (g ∣ ·)).card ≤ (Finset.Icc 1 (K / g)).card := by
        apply Finset.card_le_card_of_injOn (fun x => x / g)
        · intro x hx
          simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_setOf_eq] at hx
          simp only [Finset.coe_Icc, Set.mem_Icc]
          obtain ⟨⟨h1, h2⟩, ⟨c, rfl⟩⟩ := hx
          refine ⟨?_, Nat.div_le_div_right h2⟩
          rw [Nat.mul_div_cancel_left _ (by omega)]
          rcases Nat.eq_zero_or_pos c with h | h
          · subst h; simp at h1
          · exact h
        · intro x hx y hy h
          simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
          simp only at h
          rw [← Nat.div_mul_cancel hx.2, ← Nat.div_mul_cancel hy.2, h]
    _ = K / g := by simp

/-- `Σ_{g=2}^{K} 1/g² ≤ 3/4`. -/
lemma e102_sum_inv_sq (K : ℕ) : ∑ g ∈ Finset.Icc (2 : ℕ) K, (1 : ℝ) / (g : ℝ) ^ 2 ≤ 3 / 4 := by
  have key : ∀ K, ∑ g ∈ Finset.Icc (3 : ℕ) K, (1 : ℝ) / (g : ℝ) ^ 2 ≤ 1 / 2 - 1 / (max (K : ℝ) 2) := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rcases Nat.lt_or_ge K 2 with h | h
      · interval_cases K <;> norm_num
      · rw [Finset.sum_Icc_succ_top (by omega)]
        have hK2 : (2 : ℝ) ≤ K := by exact_mod_cast h
        rw [show max (K : ℝ) 2 = K from max_eq_left hK2] at ih
        rw [show max ((K + 1 : ℕ) : ℝ) 2 = K + 1 by push_cast; exact max_eq_left (by linarith)]
        push_cast
        have : (1 : ℝ) / (K + 1) ^ 2 ≤ 1 / K - 1 / (K + 1) := by
          rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        linarith
  rcases Nat.lt_or_ge K 2 with h | h
  · interval_cases K <;> norm_num
  · have hI : Finset.Icc (2 : ℕ) K = insert 2 (Finset.Icc 3 K) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hI, Finset.sum_insert (by simp)]
    have := key K
    norm_num at this ⊢
    have hK : (0 : ℝ) ≤ (max (K : ℝ) 2)⁻¹ := by positivity
    linarith

/-- Cardinality of a box with two special coordinates. -/
lemma e102_card_box {d : ℕ} (i0 i1 : Fin d) (h01 : i0 ≠ i1) (X Y Z : Finset ℕ) :
    (Fintype.piFinset (fun i => if i = i0 then X else if i = i1 then Y else Z)).card =
      X.card * Y.card * Z.card ^ (d - 2) := by
  rw [Fintype.card_piFinset]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i0)]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm h01, Finset.mem_univ i1⟩)]
  simp only [ite_true, if_neg (Ne.symm h01)]
  rw [Finset.prod_congr rfl (g := fun _ => Z.card) (fun i hi => by
    rw [Finset.mem_erase, Finset.mem_erase] at hi
    simp [hi.1, hi.2.1])]
  rw [Finset.prod_const, Finset.card_erase_of_mem, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_fin]
  · rw [show d - 1 - 1 = d - 2 by omega]; ring
  · exact Finset.mem_erase.mpr ⟨Ne.symm h01, Finset.mem_univ _⟩

/-- C2 (combinatorial form): many vectors in the box have coprime first two coordinates. -/
lemma e102_C2_card {d : ℕ} (i0 i1 : Fin d) (h01 : i0 ≠ i1) (K : ℕ)
    (Big : Finset (Fin d → ℕ)) (hBig : Big = Fintype.piFinset (fun i => if i = i0 then
      Finset.Ioc (K / 2) K else if i = i1 then Finset.Icc 1 K else Finset.Icc 1 K)) :
    (Big.card : ℝ) - ∑ g ∈ Finset.Icc 2 K,
        ((((Finset.Ioc (K / 2) K).filter (g ∣ ·)).card * ((Finset.Icc 1 K).filter (g ∣ ·)).card *
          K ^ (d - 2) : ℕ) : ℝ) ≤ (Big.filter (fun v => Nat.Coprime (v i0) (v i1))).card := by
  set Bad := fun g : ℕ => Fintype.piFinset (fun i => if i = i0 then (Finset.Ioc (K / 2) K).filter (g ∣ ·)
      else if i = i1 then (Finset.Icc 1 K).filter (g ∣ ·) else Finset.Icc 1 K)
  have hsub : Big.filter (fun v => ¬ Nat.Coprime (v i0) (v i1)) ⊆ (Finset.Icc 2 K).biUnion Bad := by
    intro v hv
    rw [Finset.mem_filter] at hv
    obtain ⟨hvB, hnc⟩ := hv
    rw [hBig] at hvB
    have hvB' := Fintype.mem_piFinset.mp hvB
    have h0 := hvB' i0; simp only [ite_true, Finset.mem_Ioc] at h0
    have h1 := hvB' i1; simp only [if_neg (Ne.symm h01), ite_true, Finset.mem_Icc] at h1
    set g := Nat.gcd (v i0) (v i1)
    have hg1 : g ≠ 1 := hnc
    have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
    have hgle : g ≤ v i0 := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)
    rw [Finset.mem_biUnion]
    refine ⟨g, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, Fintype.mem_piFinset.mpr fun i => ?_⟩
    by_cases hi0 : i = i0
    · subst hi0; simp only [ite_true, Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨h0, Nat.gcd_dvd_left _ _⟩
    · by_cases hi1 : i = i1
      · subst hi1; simp only [if_neg hi0, ite_true, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨h1, Nat.gcd_dvd_right _ _⟩
      · simp only [if_neg hi0, if_neg hi1]
        have := hvB' i; simp only [if_neg hi0, if_neg hi1] at this; exact this
  have hsplit := Finset.card_filter_add_card_filter_not (s := Big)
    (p := fun v => Nat.Coprime (v i0) (v i1))
  have hbad : (Big.filter (fun v => ¬ Nat.Coprime (v i0) (v i1))).card ≤
      ∑ g ∈ Finset.Icc 2 K, (((Finset.Ioc (K / 2) K).filter (g ∣ ·)).card *
        ((Finset.Icc 1 K).filter (g ∣ ·)).card * K ^ (d - 2)) := by
    refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans (le_of_eq ?_))
    refine Finset.sum_congr rfl (fun g _ => ?_)
    rw [e102_card_box i0 i1 h01]; simp
  have : ((Big.filter (fun v => ¬ Nat.Coprime (v i0) (v i1))).card : ℝ) ≤
      ∑ g ∈ Finset.Icc 2 K, ((((Finset.Ioc (K / 2) K).filter (g ∣ ·)).card *
        ((Finset.Icc 1 K).filter (g ∣ ·)).card * K ^ (d - 2) : ℕ) : ℝ) := by
    rw [← Nat.cast_sum]; exact_mod_cast hbad
  have hs : ((Big.filter (fun v => Nat.Coprime (v i0) (v i1))).card : ℝ) +
      ((Big.filter (fun v => ¬ Nat.Coprime (v i0) (v i1))).card : ℝ) = Big.card := by
    exact_mod_cast hsplit
  linarith

lemma e102_harm_le (K : ℕ) (hK : 1 ≤ K) : ∑ g ∈ Finset.Icc 2 K, (1 : ℝ) / g ≤ 1 + Real.log K := by
  have h := harmonic_le_one_add_log K
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  have : ∑ g ∈ Finset.Icc 2 K, (1 : ℝ) / g ≤ ∑ i ∈ Finset.Icc 1 K, ((i : ℝ))⁻¹ := by
    simp only [one_div]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun x hx => by simp only [Finset.mem_Icc] at hx ⊢; omega) (fun _ _ _ => by positivity)
  linarith

/-- C2 (numeric form): for `K ≥ 10⁴`, at least `K^d / 16` vectors. -/
lemma e102_C2 {d : ℕ} (hd : 2 ≤ d) (i0 i1 : Fin d) (h01 : i0 ≠ i1) (K : ℕ) (hK : 10000 ≤ K)
    (Big : Finset (Fin d → ℕ)) (hBig : Big = Fintype.piFinset (fun i => if i = i0 then
      Finset.Ioc (K / 2) K else if i = i1 then Finset.Icc 1 K else Finset.Icc 1 K)) :
    (K : ℝ) ^ d / 16 ≤ (Big.filter (fun v => Nat.Coprime (v i0) (v i1))).card := by
  have hC := e102_C2_card i0 i1 h01 K Big hBig
  have hKR : (10000 : ℝ) ≤ K := by exact_mod_cast hK
  have hBigc : (Big.card : ℝ) = ((K - K / 2 : ℕ) : ℝ) * (K : ℝ) ^ (d - 1) := by
    rw [hBig, e102_card_box i0 i1 h01]; simp
    have : (K : ℝ) ^ (d - 1) = K * K ^ (d - 2) := by
      rw [← pow_succ']; congr 1; omega
    rw [this]; ring
  have hA : (K : ℝ) / 2 ≤ ((K - K / 2 : ℕ) : ℝ) := by
    have h1 : (K / 2 : ℕ) * 2 ≤ K := Nat.div_mul_le_self K 2
    have : ((K / 2 : ℕ) : ℝ) * 2 ≤ K := by exact_mod_cast h1
    rw [Nat.cast_sub (Nat.div_le_self K 2)]; linarith
  have hterm : ∀ g ∈ Finset.Icc 2 K,
      ((((Finset.Ioc (K / 2) K).filter (g ∣ ·)).card * ((Finset.Icc 1 K).filter (g ∣ ·)).card *
        K ^ (d - 2) : ℕ) : ℝ) ≤ (K : ℝ) ^ (d - 2) * ((K : ℝ) ^ 2 / 2 * (1 / (g : ℝ) ^ 2) + 3 * K * (1 / g)) := by
    intro g hg
    have hg1 : 1 ≤ g := by simp only [Finset.mem_Icc] at hg; omega
    have hgR : (1 : ℝ) ≤ g := by exact_mod_cast hg1
    have h1 := e102_mult_Ioc (K / 2) K g hg1
    have h2 := e102_mult_Icc K g hg1
    have h1R : ((((Finset.Ioc (K / 2) K).filter (g ∣ ·)).card : ℕ) : ℝ) ≤ (K : ℝ) / (2 * g) + 3 := by
      have : (((K - K / 2) / g + 2 : ℕ) : ℝ) ≤ (K : ℝ) / (2 * g) + 3 := by
        push_cast
        have e1 : (((K - K / 2) / g : ℕ) : ℝ) ≤ ((K - K / 2 : ℕ) : ℝ) / g := Nat.cast_div_le
        have e2 : ((K - K / 2 : ℕ) : ℝ) ≤ K / 2 + 1 := by
          have h3 : K ≤ 2 * (K / 2) + 1 := by omega
          have : (K : ℝ) ≤ 2 * ((K / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast h3
          rw [Nat.cast_sub (Nat.div_le_self K 2)]; linarith
        have e3 : ((K - K / 2 : ℕ) : ℝ) / g ≤ (K / 2 + 1) / g := div_le_div_of_nonneg_right e2 (by positivity)
        have e4 : ((K : ℝ) / 2 + 1) / g ≤ K / (2 * g) + 1 := by
          rw [add_div, div_div]
          have : (1 : ℝ) / g ≤ 1 := by rw [div_le_one (by positivity)]; exact hgR
          linarith
        linarith
      exact le_trans (by exact_mod_cast h1) this
    have h2R : ((((Finset.Icc 1 K).filter (g ∣ ·)).card : ℕ) : ℝ) ≤ (K : ℝ) / g := by
      exact le_trans (by exact_mod_cast h2) Nat.cast_div_le
    push_cast
    have hKp : (0 : ℝ) ≤ (K : ℝ) ^ (d - 2) := by positivity
    have hc2 : (0 : ℝ) ≤ ((((Finset.Icc 1 K).filter (g ∣ ·)).card : ℕ) : ℝ) := by positivity
    calc ((((Finset.Ioc (K / 2) K).filter (g ∣ ·)).card : ℝ)) * (((Finset.Icc 1 K).filter (g ∣ ·)).card : ℝ) *
          (K : ℝ) ^ (d - 2) ≤ ((K : ℝ) / (2 * g) + 3) * ((K : ℝ) / g) * (K : ℝ) ^ (d - 2) := by
          apply mul_le_mul_of_nonneg_right _ hKp
          exact mul_le_mul h1R h2R hc2 (by positivity)
      _ = (K : ℝ) ^ (d - 2) * ((K : ℝ) ^ 2 / 2 * (1 / (g : ℝ) ^ 2) + 3 * K * (1 / g)) := by
          field_simp
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hsq := e102_sum_inv_sq K
  have hh := e102_harm_le K (by omega)
  have hlog : Real.log K ≤ 2 * Real.sqrt K := by
    have := Real.log_le_rpow_div (x := K) (ε := 1 / 2) (by positivity) (by norm_num)
    rw [Real.sqrt_eq_rpow]; linarith
  have hsK : (100 : ℝ) ≤ Real.sqrt K := by
    rw [show (100 : ℝ) = Real.sqrt 10000 by rw [show (10000 : ℝ) = 100 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hKR
  have hsq2 : Real.sqrt K * Real.sqrt K = K := Real.mul_self_sqrt (by positivity)
  have hpow : (K : ℝ) ^ d = (K : ℝ) ^ (d - 2) * K ^ 2 := by
    rw [← pow_add]; congr 1; omega
  have hKp : (0 : ℝ) < (K : ℝ) ^ (d - 2) := by positivity
  -- main inequality inside the bracket
  have inner : (K : ℝ) ^ 2 / 16 ≤ (K : ℝ) / 2 * K - ((K : ℝ) ^ 2 / 2 * (3 / 4) + 3 * K * (1 + 2 * Real.sqrt K)) := by
    nlinarith
  have hB : (Big.card : ℝ) ≥ (K : ℝ) / 2 * K * K ^ (d - 2) := by
    rw [hBigc]
    have : (K : ℝ) ^ (d - 1) = K * K ^ (d - 2) := by rw [← pow_succ']; congr 1; omega
    rw [this]
    have h0 : (0 : ℝ) ≤ K * K ^ (d - 2) := by positivity
    nlinarith
  have hS : ∑ g ∈ Finset.Icc 2 K, ((((Finset.Ioc (K / 2) K).filter (g ∣ ·)).card *
      ((Finset.Icc 1 K).filter (g ∣ ·)).card * K ^ (d - 2) : ℕ) : ℝ) ≤
      (K : ℝ) ^ (d - 2) * ((K : ℝ) ^ 2 / 2 * (3 / 4) + 3 * K * (1 + 2 * Real.sqrt K)) := by
    refine hsum.trans ?_
    apply mul_le_mul_of_nonneg_left _ hKp.le
    have hK0 : (0 : ℝ) ≤ K := by positivity
    have := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ (K : ℝ) ^ 2 / 2)
    have := mul_le_mul_of_nonneg_left (hh.trans (by linarith : 1 + Real.log K ≤ 1 + 2 * Real.sqrt K))
      (by positivity : (0 : ℝ) ≤ 3 * K)
    linarith
  rw [hpow]
  have := mul_le_mul_of_nonneg_left inner hKp.le
  nlinarith

/-- A2: signed-digit uniqueness. -/
lemma e102_digits (B : ℤ) (hB : 1 < B) : ∀ (N : ℕ) (c : ℕ → ℤ), (∀ e < N, |c e| < B) →
    ∑ e ∈ Finset.range N, c e * B ^ e = 0 → ∀ e < N, c e = 0 := by
  intro N
  induction N with
  | zero => intro c _ _ e he; omega
  | succ N ih =>
    intro c hc hs
    rw [Finset.sum_range_succ'] at hs
    simp only [pow_zero, mul_one] at hs
    have hsplit : ∑ e ∈ Finset.range N, c (e + 1) * B ^ (e + 1) =
        B * ∑ e ∈ Finset.range N, c (e + 1) * B ^ e := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun e _ => by ring)
    rw [hsplit] at hs
    have h0 : c 0 = 0 := by
      have hdvd : B ∣ c 0 := ⟨-(∑ e ∈ Finset.range N, c (e + 1) * B ^ e), by linarith⟩
      have := hc 0 (by omega)
      obtain ⟨k, hk⟩ := hdvd
      rw [hk] at this ⊢
      rw [abs_mul, abs_of_pos (by omega : (0 : ℤ) < B)] at this
      have : |k| < 1 := by nlinarith [abs_nonneg k]
      have : k = 0 := by rw [abs_lt] at this; omega
      simp [this]
    rw [h0, add_zero] at hs
    have hs' : ∑ e ∈ Finset.range N, c (e + 1) * B ^ e = 0 := by
      rcases mul_eq_zero.mp hs with h | h
      · omega
      · exact h
    have := ih (fun e => c (e + 1)) (fun e he => hc (e + 1) (by omega)) hs'
    intro e he
    rcases e with _ | e
    · exact h0
    · exact this e (by omega)

/-- Bound for a signed-digit sum. -/
lemma e102_digit_bound (B : ℤ) (hB : 1 < B) (n : ℕ) (c : ℕ → ℤ) (hc : ∀ e < n, |c e| ≤ B - 1) :
    |∑ e ∈ Finset.range n, c e * B ^ e| ≤ B ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h1 := ih (fun e he => hc e (by omega))
    have h2 : |c n * B ^ n| ≤ (B - 1) * B ^ n := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < B ^ n)]
      exact mul_le_mul_of_nonneg_right (hc n (by omega)) (by positivity)
    calc |∑ e ∈ Finset.range n, c e * B ^ e + c n * B ^ n|
        ≤ |∑ e ∈ Finset.range n, c e * B ^ e| + |c n * B ^ n| := abs_add_le _ _
      _ ≤ (B ^ n - 1) + (B - 1) * B ^ n := add_le_add h1 h2
      _ = B ^ (n + 1) - 1 := by ring

/-- Sums over `Fin d` as sums over `range d`. -/
lemma e102_fin_range {d : ℕ} (f : Fin d → ℤ) (g : ℕ → ℤ) :
    ∑ i : Fin d, f i * g i = ∑ e ∈ Finset.range d, (if h : e < d then f ⟨e, h⟩ else 0) * g e := by
  rw [Finset.sum_range (fun e => (if h : e < d then f ⟨e, h⟩ else 0) * g e)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [i.isLt]

/-- Digits over `Fin d`. -/
lemma e102_digits_fin {d : ℕ} (B : ℤ) (hB : 1 < B) (c : Fin d → ℤ) (hc : ∀ i, |c i| < B)
    (h : ∑ i : Fin d, c i * B ^ (i : ℕ) = 0) : ∀ i, c i = 0 := by
  rw [e102_fin_range c (fun e => B ^ e)] at h
  have := e102_digits B hB d _ (fun e he => by simp only [dif_pos he]; exact hc _) h
  intro i
  have := this i i.isLt
  simpa [i.isLt] using this

/-- A1: the explicit projection. -/
noncomputable def e102phi (d : ℕ) (M : ℤ) : (Fin d → ℤ) →+ ℝ² where
  toFun x := !₂[((∑ i : Fin d, x i * M ^ (i : ℕ) : ℤ) : ℝ), ((∑ i : Fin d, x i * M ^ (d * (i : ℕ)) : ℤ) : ℝ)]
  map_zero' := by ext j; fin_cases j <;> simp
  map_add' x y := by
    ext j; fin_cases j <;> simp [add_mul, Finset.sum_add_distrib]

lemma e102_phi0 (d : ℕ) (M : ℤ) (x : Fin d → ℤ) :
    e102phi d M x 0 = ((∑ i : Fin d, x i * M ^ (i : ℕ) : ℤ) : ℝ) := rfl
lemma e102_phi1 (d : ℕ) (M : ℤ) (x : Fin d → ℤ) :
    e102phi d M x 1 = ((∑ i : Fin d, x i * M ^ (d * (i : ℕ)) : ℤ) : ℝ) := rfl


/-- The determinant identity for the projection. -/
lemma e102_det_phi (d : ℕ) (M : ℤ) (u w : Fin d → ℤ) :
    e102det (e102phi d M u) (e102phi d M w) =
      ((∑ j : Fin d, (∑ i : Fin d, (u i * w j - u j * w i) * M ^ (i : ℕ)) * (M ^ d) ^ (j : ℕ) : ℤ) : ℝ) := by
  unfold e102det
  rw [e102_phi0, e102_phi1, e102_phi0, e102_phi1, ← Int.cast_mul, ← Int.cast_mul, ← Int.cast_sub]
  congr 1
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun i j => u i * M ^ (i : ℕ) * (w j * M ^ (d * (j : ℕ)))), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← pow_mul]; ring

/-- A3: the projection with `M = 2m²` is collinearity-faithful at scale `m`. -/
lemma e102_A3 (d m : ℕ) (hm : 1 ≤ m) (u w : Fin d → ℤ) (hu : ∀ i, |u i| < m) (hw : ∀ i, |w i| < m)
    (h : e102det (e102phi d (2 * m ^ 2) u) (e102phi d (2 * m ^ 2) w) = 0) : e102Par u w := by
  set M : ℤ := 2 * m ^ 2 with hM
  have hM1 : 1 < M := by rw [hM]; nlinarith
  rw [e102_det_phi] at h
  have hD := Int.cast_eq_zero.mp h
  have hcoef : ∀ i j, |u i * w j - u j * w i| ≤ M - 1 := by
    intro i j
    have h1 := hu i; have h2 := hw j; have h3 := hu j; have h4 := hw i
    have e1 : |u i * w j| ≤ ((m : ℤ) - 1) * (m - 1) := by
      rw [abs_mul]; exact mul_le_mul (by omega) (by omega) (abs_nonneg _) (by omega)
    have e2 : |u j * w i| ≤ ((m : ℤ) - 1) * (m - 1) := by
      rw [abs_mul]; exact mul_le_mul (by omega) (by omega) (abs_nonneg _) (by omega)
    calc |u i * w j - u j * w i| ≤ |u i * w j| + |u j * w i| := abs_sub _ _
      _ ≤ 2 * (((m : ℤ) - 1) * (m - 1)) := by linarith
      _ ≤ M - 1 := by rw [hM]; nlinarith
  have hT : ∀ j, ∑ i : Fin d, (u i * w j - u j * w i) * M ^ (i : ℕ) = 0 := by
    have hMd : 1 < M ^ d ∨ d = 0 := by
      rcases Nat.eq_zero_or_pos d with h0 | h0
      · right; exact h0
      · left; exact one_lt_pow₀ hM1 (by omega)
    rcases hMd with hMd | hd0
    · refine e102_digits_fin (M ^ d) hMd _ (fun j => ?_) hD
      have := e102_digit_bound M hM1 d (fun e => if h : e < d then u ⟨e, h⟩ * w j - u j * w ⟨e, h⟩ else 0)
        (fun e he => by simp only [dif_pos he]; exact hcoef _ _)
      rw [← e102_fin_range (fun i => u i * w j - u j * w i) (fun e => M ^ e)] at this
      omega
    · subst hd0; intro j; exact j.elim0
  intro i j
  have := e102_digits_fin M hM1 (fun i => u i * w j - u j * w i)
    (fun i => by have := hcoef i j; omega) (hT j) i
  linarith

/-- A4: the projection is injective on the grid `[1, m]^d`. -/
lemma e102_A4 (d m : ℕ) (hm : 1 ≤ m) (x y : Fin d → ℤ) (hx : ∀ i, 1 ≤ x i ∧ x i ≤ m)
    (hy : ∀ i, 1 ≤ y i ∧ y i ≤ m) (h : e102phi d (2 * m ^ 2) x = e102phi d (2 * m ^ 2) y) : x = y := by
  have h0 : e102phi d (2 * m ^ 2) x 0 = e102phi d (2 * m ^ 2) y 0 := by rw [h]
  rw [e102_phi0, e102_phi0] at h0
  have h0' := Int.cast_injective h0
  have hsum : ∑ i : Fin d, (x i - y i) * (2 * (m : ℤ) ^ 2) ^ (i : ℕ) = 0 := by
    simp only [sub_mul, Finset.sum_sub_distrib, h0', sub_self]
  have := e102_digits_fin (2 * (m : ℤ) ^ 2) (by nlinarith) (fun i => x i - y i)
    (fun i => by
      have := hx i; have := hy i
      rw [abs_lt]; constructor <;> nlinarith) hsum
  funext i; have := this i; linarith

open scoped Classical in
/-- Assembly of (в): many rich lines. -/
lemma e102_rich_lower {d : ℕ} (hd : 2 ≤ d) (m K R : ℕ) (hm : 2 ≤ m) (hKm : K < m) (hRm : R ≤ m)
    (hKR : R + 3 * K ≤ m) (hKR' : K ≤ R) (hK : 10000 ≤ K)
    (φ : (Fin d → ℤ) →+ ℝ²) (hφ : e102Faithful φ m)
    (hinj : ∀ a ∈ e102G d m, ∀ b ∈ e102G d m, φ a = φ b → a = b) :
    (K : ℝ) ^ (d + 1) * (R : ℝ) ^ (d - 1) / 32 ≤ {L : AffineSubspace ℝ ℝ² |
      IsLine L ∧ 3 < (((e102G d m).image φ).filter (· ∈ L)).card}.ncard := by
  set i0 : Fin d := ⟨0, by omega⟩
  set i1 : Fin d := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  set Big := Fintype.piFinset (fun i => if i = i0 then Finset.Ioc (K / 2) K else
      if i = i1 then Finset.Icc 1 K else Finset.Icc 1 K) with hBig
  set D := Big.filter (fun v => Nat.Coprime (v i0) (v i1))
  have hDc := e102_C2 hd i0 i1 h01 K hK Big hBig
  -- cast to ℤ
  let cz : (Fin d → ℕ) → (Fin d → ℤ) := fun v i => (v i : ℤ)
  have hcz : Function.Injective cz := fun v w h => funext fun i => by
    have := congrFun h i; simpa [cz] using this
  let S : (Fin d → ℕ) → Finset (Fin d → ℤ) := fun v =>
    Fintype.piFinset (fun i => if i = i0 then Finset.Icc (1 : ℤ) (v i0) else Finset.Icc 1 R)
  set I := D.biUnion (fun v => (S v).image (fun x => (cz v, x))) with hI
  have hmemD : ∀ v ∈ D, (∀ i, 1 ≤ v i ∧ v i ≤ K) ∧ K / 2 < v i0 ∧ Nat.Coprime (v i0) (v i1) := by
    intro v hv
    rw [Finset.mem_filter] at hv
    obtain ⟨hvB, hcop⟩ := hv
    rw [hBig, Fintype.mem_piFinset] at hvB
    have h0 := hvB i0; simp only [ite_true, Finset.mem_Ioc] at h0
    refine ⟨fun i => ?_, h0.1, hcop⟩
    have := hvB i
    by_cases hi0 : i = i0
    · subst hi0; simp only [ite_true, Finset.mem_Ioc] at this; omega
    · by_cases hi1 : i = i1
      · subst hi1; simp only [if_neg hi0, ite_true, Finset.mem_Icc] at this; exact this
      · simp only [if_neg hi0, if_neg hi1, Finset.mem_Icc] at this; exact this
  have hI_ok : ∀ p ∈ I, e102GoodDir hd K p.1 ∧ e102Start hd R p.1 p.2 := by
    intro p hp
    rw [Finset.mem_biUnion] at hp
    obtain ⟨v, hv, hp⟩ := hp
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hvK, -, hcop⟩ := hmemD v hv
    rw [Fintype.mem_piFinset] at hx
    refine ⟨⟨fun i => ?_, ?_⟩, ⟨?_, fun i => ?_⟩⟩
    · have := hvK i; simp only [cz]; constructor <;> omega
    · simp only [cz]; rw [Int.gcd_natCast_natCast]; exact hcop
    · have := hx i0; simp only [ite_true, Finset.mem_Icc] at this; simp only [cz]; exact this
    · show 1 ≤ x i ∧ x i ≤ R
      have := hx i
      by_cases hi0 : i = i0
      · rw [if_pos hi0, Finset.mem_Icc] at this
        have h2 := hvK i0
        rw [hi0]
        rw [hi0] at this
        have h3 : (v i0 : ℤ) ≤ K := by exact_mod_cast h2.2
        constructor <;> omega
      · simp only [if_neg hi0, Finset.mem_Icc] at this; exact this
  have hC5 := e102_C5 hd m K R hm hKm hRm hKR φ hφ hinj I hI_ok
  -- card of I
  have hcardS : ∀ v ∈ D, ((S v).card : ℝ) = (v i0 : ℝ) * (R : ℝ) ^ (d - 1) := by
    intro v _
    rw [Fintype.card_piFinset, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i0)]
    simp only [ite_true, Int.card_Icc]
    rw [Finset.prod_congr rfl (g := fun _ => R) (fun i hi => by
      rw [Finset.mem_erase] at hi; simp [hi.1])]
    rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin]
    push_cast; simp
  have hcardI : (I.card : ℝ) = ∑ v ∈ D, ((S v).card : ℝ) := by
    rw [hI, Finset.card_biUnion]
    · push_cast
      refine Finset.sum_congr rfl (fun v _ => ?_)
      rw [Finset.card_image_of_injective _ (fun x y h => by simpa using h)]
    · intro v _ w _ hvw
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro p hp hp'
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨y, -, hy⟩ := Finset.mem_image.mp hp'
      exact hvw (hcz (congrArg Prod.fst hy).symm)
  have hlow : (K : ℝ) / 2 * (R : ℝ) ^ (d - 1) * D.card ≤ I.card := by
    rw [hcardI, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_le_sum (fun v hv => ?_)
    rw [hcardS v hv]
    obtain ⟨-, h2, -⟩ := hmemD v hv
    have : (K : ℝ) / 2 ≤ (v i0 : ℝ) := by
      have h3 : K ≤ 2 * v i0 := by omega
      have : (K : ℝ) ≤ 2 * (v i0 : ℝ) := by exact_mod_cast h3
      linarith
    have hR0 : (0 : ℝ) ≤ (R : ℝ) ^ (d - 1) := by positivity
    push_cast; nlinarith
  have hC5R : (I.card : ℝ) ≤ {L : AffineSubspace ℝ ℝ² |
      IsLine L ∧ 3 < (((e102G d m).image φ).filter (· ∈ L)).card}.ncard := by exact_mod_cast hC5
  have hpow : (K : ℝ) ^ (d + 1) = K * K ^ d := by ring
  have hR0 : (0 : ℝ) ≤ (R : ℝ) ^ (d - 1) := by positivity
  have hK0 : (0 : ℝ) ≤ K := by positivity
  have : (K : ℝ) ^ (d + 1) * (R : ℝ) ^ (d - 1) / 32 ≤ (K : ℝ) / 2 * (R : ℝ) ^ (d - 1) * D.card := by
    rw [hpow]
    have := mul_le_mul_of_nonneg_left hDc (by positivity : (0 : ℝ) ≤ (K : ℝ) / 2 * (R : ℝ) ^ (d - 1))
    nlinarith
  linarith

/-- Extra points on a parabola in the left half-plane. -/
noncomputable def e102ext (k : ℕ) : Finset ℝ² :=
  (Finset.Icc 1 k).image (fun t : ℕ => !₂[-(t : ℝ), (t : ℝ) ^ 2])

lemma e102_ext_inj (k : ℕ) : Set.InjOn (fun t : ℕ => (!₂[-(t : ℝ), (t : ℝ) ^ 2] : ℝ²)) (Finset.Icc 1 k) := by
  intro s _ t _ h
  have := congrArg (fun p : ℝ² => p 0) h
  simp at this; exact_mod_cast this

lemma e102_ext_card (k : ℕ) : (e102ext k).card = k := by
  rw [e102ext, Finset.card_image_of_injOn (e102_ext_inj k)]; simp

open scoped Classical in
/-- D1: a line contains at most two of the extra points. -/
lemma e102_ext_line (k : ℕ) (L : AffineSubspace ℝ ℝ²) (hL : IsLine L) :
    ((e102ext k).filter (· ∈ L)).card ≤ 2 := by
  by_contra hc
  push Not at hc
  obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr⟩ := Finset.two_lt_card.mp hc
  rw [Finset.mem_filter] at hp hq hr
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hp.1
  obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hq.1
  obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hr.1
  have hdet := e102_B1 L hL _ _ _ hp.2 hq.2 hr.2
  have hab : (a : ℝ) ≠ b := fun h => hpq (by rw [show a = b by exact_mod_cast h])
  have hac : (a : ℝ) ≠ c := fun h => hpr (by rw [show a = c by exact_mod_cast h])
  have hbc : (b : ℝ) ≠ c := fun h => hqr (by rw [show b = c by exact_mod_cast h])
  simp only [e102det, PiLp.sub_apply] at hdet
  simp at hdet
  have : ((b : ℝ) - a) * ((c : ℝ) - a) * ((c : ℝ) - b) = 0 := by linear_combination -hdet
  rcases mul_eq_zero.mp this with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact hab (by linarith)
    · exact hac (by linarith)
  · exact hbc (by linarith)

lemma e102_G_card (d m : ℕ) : (e102G d m).card = m ^ d := by
  simp [e102G, Fintype.card_piFinset]

open scoped Classical in
/-- D2: the padded configuration. -/
lemma e102_config {d : ℕ} (hd : 2 ≤ d) (m k : ℕ) (hm : 40004 ≤ m) :
    ∃ P : Finset ℝ², P.card = m ^ d + k ∧
      (∀ L : AffineSubspace ℝ ℝ², IsLine L → (P.filter (· ∈ L)).card ≤ m + 2) ∧
      ((m / 4 : ℕ) : ℝ) ^ (d + 1) * ((m / 4 : ℕ) : ℝ) ^ (d - 1) / 32 ≤
        {L : AffineSubspace ℝ ℝ² | IsLine L ∧ 3 < (P.filter (· ∈ L)).card}.ncard := by
  set φ := e102phi d (2 * m ^ 2)
  have hφ : e102Faithful φ m := fun u w hu hw h => e102_A3 d m (by omega) u w hu hw h
  have hinj : ∀ a ∈ e102G d m, ∀ b ∈ e102G d m, φ a = φ b → a = b := fun a ha b hb h =>
    e102_A4 d m (by omega) a b (e102_memG.mp ha) (e102_memG.mp hb) h
  set Q := (e102G d m).image φ
  have hdisj : Disjoint Q (e102ext k) := by
    rw [Finset.disjoint_left]
    intro p hp hp'
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨t, ht, ht'⟩ := Finset.mem_image.mp hp'
    have h1 := congrArg (fun p : ℝ² => p 0) ht'
    simp only at h1
    rw [show (φ x) 0 = _ from e102_phi0 d (2 * m ^ 2) x] at h1
    have hxpos : 0 < ∑ i : Fin d, x i * (2 * (m : ℤ) ^ 2) ^ (i : ℕ) := by
      apply Finset.sum_pos
      · intro i _
        have := (e102_memG.mp hx i).1
        have : (0 : ℤ) < (2 * (m : ℤ) ^ 2) ^ (i : ℕ) := by positivity
        positivity
      · exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast (Finset.mem_Icc.mp ht).1
    simp at h1
    have : (0 : ℝ) < ((∑ i : Fin d, x i * (2 * (m : ℤ) ^ 2) ^ (i : ℕ) : ℤ) : ℝ) := by exact_mod_cast hxpos
    push_cast at this
    linarith
  refine ⟨Q ∪ e102ext k, ?_, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hdisj, e102_ext_card, Finset.card_image_of_injOn
      (fun a ha b hb h => hinj a ha b hb h), e102_G_card]
  · intro L hL
    rw [Finset.filter_union]
    refine (Finset.card_union_le _ _).trans ?_
    have h1 : (Q.filter (· ∈ L)).card ≤ m := e102_B3 m (by omega) φ hφ L hL
    have := e102_ext_line k L hL
    omega
  · have hrich := e102_rich_lower hd m (m / 4) (m / 4) (by omega) (by omega) (by omega)
      (by omega) le_rfl (by omega) φ hφ hinj
    refine hrich.trans (Nat.cast_le.mpr (Set.ncard_le_ncard ?_ (e102_rich_finite _)))
    intro L ⟨hL, h3⟩
    exact ⟨hL, lt_of_lt_of_le h3 (Finset.card_le_card
      (Finset.filter_subset_filter _ Finset.subset_union_left))⟩

/-- E1: arithmetic of `m = ⌊n^{1/d}⌋₊`. -/
lemma e102_floor_root {d : ℕ} (hd : 1 ≤ d) (n : ℕ) (hn : 40004 ^ d ≤ n) :
    let m := ⌊(n : ℝ) ^ (1 / (d : ℝ))⌋₊
    40004 ≤ m ∧ m ^ d ≤ n ∧ n < (m + 1) ^ d ∧ (m : ℝ) ≤ (n : ℝ) ^ (1 / (d : ℝ)) := by
  intro m
  set x := (n : ℝ) ^ (1 / (d : ℝ)) with hx
  have hx0 : 0 ≤ x := by positivity
  have hxd : x ^ d = n := by
    rw [hx, one_div]; exact Real.rpow_inv_natCast_pow (by positivity) (by omega)
  have hmx : (m : ℝ) ≤ x := Nat.floor_le hx0
  have hxm : x < m + 1 := Nat.lt_floor_add_one x
  refine ⟨?_, ?_, ?_, hmx⟩
  · apply Nat.le_floor
    by_contra hlt
    push_neg at hlt
    have : x ^ d < ((40004 : ℕ) : ℝ) ^ d := pow_lt_pow_left₀ hlt hx0 (by omega)
    rw [hxd] at this
    have : (n : ℝ) < ((40004 ^ d : ℕ) : ℝ) := by push_cast at this ⊢; linarith
    have := Nat.cast_lt.mp this
    omega
  · have : (m : ℝ) ^ d ≤ x ^ d := pow_le_pow_left₀ (by positivity) hmx d
    rw [hxd] at this
    exact_mod_cast this
  · have : x ^ d < ((m : ℝ) + 1) ^ d := pow_lt_pow_left₀ hxm hx0 (by omega)
    rw [hxd] at this
    exact_mod_cast this

/-- E2: the main bound for `d ≥ 2` in FC terms. -/
lemma e102_main {d : ℕ} (hd : 2 ≤ d) :
    ∀ᶠ n : ℕ in Filter.atTop, Erdos102.h (1 / (32 * 100 ^ d)) n ≤
      (⌈3 * (n : ℝ) ^ (1 / (d : ℝ))⌉₊ : ℕ∞) := by
  rw [Filter.eventually_atTop]
  refine ⟨40004 ^ d, fun n hn => ?_⟩
  obtain ⟨hm, hmd, hmd', hmx⟩ := e102_floor_root (by omega : 1 ≤ d) n hn
  set m := ⌊(n : ℝ) ^ (1 / (d : ℝ))⌋₊
  obtain ⟨P, hcard, hline, hrich⟩ := e102_config hd m (n - m ^ d) hm
  have hcard' : P.card = n := by rw [hcard]; omega
  have hadm : Erdos102.Admissible (1 / (32 * 100 ^ d)) n P := by
    refine ⟨hcard', ?_⟩
    unfold Erdos102.richLineCount Erdos102.pointsOn
    refine le_trans ?_ hrich
    set q := m / 4
    have hq : m + 1 ≤ 10 * q := by omega
    have h1 : (n : ℝ) ≤ (10 * q : ℝ) ^ d := by
      have : n ≤ (10 * q) ^ d := le_trans hmd'.le (Nat.pow_le_pow_left hq d)
      exact_mod_cast this
    have h2 : (n : ℝ) ^ 2 ≤ ((10 * q : ℝ) ^ d) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    have h3 : ((10 * q : ℝ) ^ d) ^ 2 = 100 ^ d * ((q : ℝ) ^ (d + 1) * (q : ℝ) ^ (d - 1)) := by
      calc ((10 * q : ℝ) ^ d) ^ 2 = (100 * (q : ℝ) ^ 2) ^ d := by
            rw [← pow_mul, mul_comm d 2, pow_mul]; ring
        _ = _ := by rw [mul_pow, ← pow_mul, ← pow_add, show d + 1 + (d - 1) = 2 * d by omega]
    rw [h3] at h2
    have h100 : (0 : ℝ) < 100 ^ d := by positivity
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hmax : Erdos102.maxCollinear P ≤ m + 2 := by
    by_contra hc
    push_neg at hc
    obtain ⟨L, hL, hk⟩ := (Erdos102.le_maxCollinear_iff P (m + 3)).mp (by omega)
    have := hline L hL
    unfold Erdos102.pointsOn at hk
    omega
  refine (iInf_le_of_le P (iInf_le_of_le hadm le_rfl)).trans ?_
  have hx1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 / (d : ℝ)) := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    linarith
  have : ((m + 2 : ℕ) : ℝ) ≤ ⌈3 * (n : ℝ) ^ (1 / (d : ℝ))⌉₊ := by
    push_cast
    linarith [Nat.le_ceil (3 * (n : ℝ) ^ (1 / (d : ℝ)))]
  have : m + 2 ≤ ⌈3 * (n : ℝ) ^ (1 / (d : ℝ))⌉₊ := by exact_mod_cast this
  exact_mod_cast hmax.trans this

/--
Let $c > 0$ and let $h_c(n)$ be such that for any $n$ points in $\mathbb{R}^2$ with at least
$cn^2$ lines that each contain more than three of the points, some line contains $h_c(n)$ of
the points. Is it true that, for fixed $c > 0$, $h_c(n) \to \infty$?
-/
@[category research open, AMS 52]
theorem erdos_102 :
    answer(sorry) ↔ ∀ c > 0, ∀ M : ℕ, ∀ᶠ n in atTop, (M : ℕ∞) ≤ h c n := by
  sorry

/--
It is not known whether $h_c(n) \geq 5$ for all sufficiently large $n$.
-/
@[category research open, AMS 52]
theorem erdos_102.variants.five :
    answer(sorry) ↔ ∀ c > 0, ∀ᶠ n in atTop, (5 : ℕ∞) ≤ h c n := by
  sorry

/--
It is easy to see that $h_c(n) \ll_c n^{1/2}$: for all sufficiently small $c > 0$ there are
admissible configurations (e.g. grids) in which no line contains more than $C_c n^{1/2}$ points.
-/
@[category research solved, AMS 52]
theorem erdos_102.variants.upper_sqrt :
    ∃ c₀ > (0 : ℝ), ∀ c ∈ Set.Ioc 0 c₀, ∃ C : ℝ, ∀ᶠ n in atTop,
      h c n ≤ (⌈C * Real.sqrt n⌉₊ : ℕ∞) := by
  refine ⟨1 / (32 * 100 ^ 2), by positivity, fun c hc => ⟨3, ?_⟩⟩
  filter_upwards [e102_main (le_refl 2)] with n hn
  refine le_trans ?_ (hn.trans (le_of_eq ?_))
  · unfold h
    refine le_iInf fun P => le_iInf fun hP => iInf_le_of_le P (iInf_le_of_le ⟨hP.1, ?_⟩ le_rfl)
    exact le_trans (mul_le_mul_of_nonneg_right hc.2 (by positivity)) hP.2
  · rw [Real.sqrt_eq_rpow]; norm_num

/--
Erdős [Er95] suggested that perhaps $h_c(n) \gg_c n^{1/2}$. Zach Hunter pointed out that this is
false: the points of $\{1, \dots, m\}^d$ with $n \approx m^d$, randomly projected to
$\mathbb{R}^2$, meet every line in $\ll_d n^{1/d}$ points and determine $\gg_d n^2$ lines with
more than three points. This gives $h_c(n) \ll n^{1 / \log(1/c)}$; we state the underlying form:
for every $d \geq 1$ there is $c > 0$ with $h_c(n) \ll_d n^{1/d}$.
-/
@[category research solved, AMS 52]
theorem erdos_102.variants.hunter :
    ∀ d : ℕ, 1 ≤ d → ∃ c > (0 : ℝ), ∃ C : ℝ, ∀ᶠ n in atTop,
      h c n ≤ (⌈C * (n : ℝ) ^ (1 / (d : ℝ))⌉₊ : ℕ∞) := by
  sorry

end Erdos102
