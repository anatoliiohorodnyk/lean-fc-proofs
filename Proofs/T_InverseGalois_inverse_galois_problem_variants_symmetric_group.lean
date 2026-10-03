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
# Inverse Galois problem

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Inverse_Galois_problem)
-/

@[expose] public section

namespace InverseGalois

structure GaloisRealization.{u, v} (K : Type u) (G : Type v) [Field K] [Group G] where
  -- Every Galois extension of `K : Type u` injects into `AlgebraicClosure K : Type u`.
  -- We therefore lose no generality assuming `L : Type u`.
  L : Type u
  to_field : Field L
  to_algebra : Algebra K L
  to_isGalois : IsGalois K L
  iso : G ≃* (L ≃ₐ[K] L)

/--
Say a group `G` is realizable over a field `K` if it
is isomorphic to the Galois group of a Galois extension
of `K`
-/
class IsRealizable (K G : Type*) [Field K] [Group G] where
  exists_realization : Nonempty (GaloisRealization K G)

/--
The **Inverse Galois Problem**: every finite group is
isomorphic to the Galois group of a Galois extension of the
rationals.
-/
@[category research open, AMS 12]
theorem inverse_galois_problem {G : Type*} [Fintype G] [Group G] :
    IsRealizable ℚ G := by
  sorry

/--
Every finite cyclic group is realizable.
-/
@[category research solved, AMS 12]
theorem inverse_galois_problem.variants.cyclic
    {G : Type*} [Fintype G] [Group G] [IsCyclic G] :
    IsRealizable ℚ G := by
  sorry

/--
Every finite abelian group is realizable.
-/
@[category research solved, AMS 12]
theorem inverse_galois_problem.variants.abelian
    {G : Type*} [Fintype G] [CommGroup G] :
    IsRealizable ℚ G := by
  sorry

open Polynomial NumberField in
lemma sn_f_ne_zero {k : Type*} [Field k] (n : ℕ) (hn : 2 ≤ n) : (X ^ n - X - 1 : k[X]) ≠ 0 := by
  intro h
  have := congrArg (coeff · 0) h
  simp at this
  rw [if_neg (by omega)] at this
  simp at this

open Polynomial NumberField in
/-- Facts at a multiple root of `Xⁿ - X - 1`. -/
lemma sn_double_root {k : Type*} [Field k] (n : ℕ) (hn : 2 ≤ n) (a : k)
    (h : 1 < rootMultiplicity a (X ^ n - X - 1 : k[X])) :
    (n : k) ≠ 0 ∧ (n : k) - 1 ≠ 0 ∧ a ≠ 0 ∧ ((n : k) - 1) * a = -n := by
  rw [one_lt_rootMultiplicity_iff_isRoot (sn_f_ne_zero n hn)] at h
  obtain ⟨h0, h1⟩ := h
  simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_one, derivative_sub, derivative_X_pow,
    derivative_X, derivative_one, sub_zero, eval_mul, eval_C, eval_natCast] at h0 h1
  have hpow : a ^ n = a * a ^ (n - 1) := by
    rw [← pow_succ', show n - 1 + 1 = n by omega]
  have hn0 : (n : k) ≠ 0 := by intro hz; rw [hz] at h1; simp at h1
  have ha0 : a ≠ 0 := by
    intro hz; rw [hz, zero_pow (by omega)] at h1; simp at h1
  have key : ((n : k) - 1) * a = -n := by
    have e1 : (n : k) * a ^ n = a := by rw [hpow]; linear_combination a * h1
    linear_combination e1 - (n : k) * h0
  have hn1 : (n : k) - 1 ≠ 0 := by
    intro hz; rw [hz, zero_mul] at key; exact hn0 (neg_eq_zero.mp key.symm)
  exact ⟨hn0, hn1, ha0, key⟩

open Polynomial NumberField in
/-- S1a: at most one multiple root. -/
lemma sn_unique_double {k : Type*} [Field k] (n : ℕ) (hn : 2 ≤ n) (a b : k)
    (ha : 1 < rootMultiplicity a (X ^ n - X - 1 : k[X]))
    (hb : 1 < rootMultiplicity b (X ^ n - X - 1 : k[X])) : a = b := by
  obtain ⟨-, h1, -, ka⟩ := sn_double_root n hn a ha
  obtain ⟨-, -, -, kb⟩ := sn_double_root n hn b hb
  have : ((n : k) - 1) * (a - b) = 0 := by linear_combination ka - kb
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h1)

open Polynomial NumberField in
/-- S1b: multiplicities are at most two. -/
lemma sn_mult_le_two {k : Type*} [Field k] (n : ℕ) (hn : 2 ≤ n) (a : k) :
    rootMultiplicity a (X ^ n - X - 1 : k[X]) ≤ 2 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨hn0, hn1, ha0, -⟩ := sn_double_root n hn a (by omega)
  have h2 := isRoot_iterate_derivative_of_lt_rootMultiplicity (n := 2) hlt
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id,
    derivative_sub, derivative_X_pow, derivative_X, derivative_one, sub_zero, derivative_mul,
    derivative_C, zero_mul, zero_add, IsRoot, eval_mul, eval_C, eval_pow, eval_X,
    eval_natCast, derivative_natCast] at h2
  have hc : ((n - 1 : ℕ) : k) = (n : k) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rw [hc] at h2
  have : a ^ (n - 1 - 1) ≠ 0 := pow_ne_zero _ ha0
  simp_all

open Polynomial NumberField in
lemma sn_monic {R : Type*} [CommRing R] [Nontrivial R] (n : ℕ) (hn : 2 ≤ n) :
    (X ^ n - X - 1 : R[X]).Monic := by
  rw [sub_sub]
  apply monic_X_pow_sub
  calc (X + 1 : R[X]).degree ≤ 1 := by compute_degree
    _ < n := by exact_mod_cast (show 1 < n by omega)

open Polynomial NumberField in
lemma sn_natDegree {R : Type*} [CommRing R] [Nontrivial R] (n : ℕ) (hn : 2 ≤ n) :
    (X ^ n - X - 1 : R[X]).natDegree = n := by
  rw [sub_sub, natDegree_sub_eq_left_of_natDegree_lt] <;> [simp; (rw [natDegree_X_pow]; calc
    (X + 1 : R[X]).natDegree ≤ 1 := by compute_degree
    _ < n := by omega)]

open Polynomial NumberField in
/-- Residue count: over a field where `Xⁿ - X - 1` splits, it has at least `n - 1` distinct roots. -/
lemma sn_res_count {κ : Type*} [Field κ] [DecidableEq κ] (n : ℕ) (hn : 2 ≤ n)
    (hs : (X ^ n - X - 1 : κ[X]).Splits) :
    n ≤ (X ^ n - X - 1 : κ[X]).roots.toFinset.card + 1 := by
  set M := (X ^ n - X - 1 : κ[X]).roots
  have hcard : M.card = n := by
    rw [splits_iff_card_roots.mp hs, sn_natDegree n hn]
  have hsum : ∑ x ∈ M.toFinset, M.count x = n := by
    rw [Multiset.toFinset_sum_count_eq, hcard]
  have hle : ∀ x ∈ M.toFinset, M.count x ≤ 1 + (if 2 ≤ M.count x then 1 else 0) := by
    intro x _
    have := sn_mult_le_two n hn x
    rw [count_roots] at *
    split_ifs <;> omega
  have hone : (M.toFinset.filter (fun x => 2 ≤ M.count x)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    simp only [Finset.mem_filter] at ha hb
    have hc : ∀ x, M.count x = rootMultiplicity x (X ^ n - X - 1 : κ[X]) :=
      fun x => count_roots _
    rw [hc] at ha hb
    exact sn_unique_double n hn a b (by omega) (by omega)
  calc n = ∑ x ∈ M.toFinset, M.count x := hsum.symm
    _ ≤ ∑ x ∈ M.toFinset, (1 + (if 2 ≤ M.count x then 1 else 0)) := Finset.sum_le_sum hle
    _ = M.toFinset.card + (M.toFinset.filter (fun x => 2 ≤ M.count x)).card := by
      rw [Finset.sum_add_distrib, Finset.sum_boole]; simp
    _ ≤ M.toFinset.card + 1 := by omega

open Polynomial NumberField in
/-- Roots of `Xⁿ - X - 1` in `L` are algebraic integers; the polynomial splits over `𝓞 L`. -/
lemma sn_rootsO {L : Type} [Field L] [NumberField L] (n : ℕ) (hn : 2 ≤ n)
    (hs : (X ^ n - X - 1 : L[X]).Splits) :
    (X ^ n - X - 1 : (𝓞 L)[X]).Splits ∧ (X ^ n - X - 1 : (𝓞 L)[X]).roots.Nodup := by
  set fO : (𝓞 L)[X] := X ^ n - X - 1
  set fL : L[X] := X ^ n - X - 1
  have hinj : Function.Injective (algebraMap (𝓞 L) L) := FaithfulSMul.algebraMap_injective _ _
  have hmap : map (algebraMap (𝓞 L) L) fO = fL := by simp [fO, fL]
  have hsep : fL.Separable := by
    have h1 := (Irreducible.separable (X_pow_sub_X_sub_one_irreducible_rat (n := n) (by omega)))
    have := h1.map (f := algebraMap ℚ L)
    simpa using this
  have hLnd : fL.roots.Nodup := nodup_roots hsep
  have hLcard : fL.roots.card = n := by
    rw [splits_iff_card_roots.mp hs, sn_natDegree n hn]
  have hO0 : fO ≠ 0 := (sn_monic n hn).ne_zero
  have hle := map_roots_le_of_injective fO hinj
  rw [hmap] at hle
  have hOnd : fO.roots.Nodup := (Multiset.nodup_of_le hle hLnd).of_map _
  have hsub : fL.roots ⊆ fO.roots.map (algebraMap (𝓞 L) L) := by
    intro α hα
    have hroot : eval α fL = 0 := (mem_roots (sn_monic n hn).ne_zero).mp hα
    have hint : IsIntegral ℤ α := by
      refine ⟨X ^ n - X - 1, sn_monic n hn, ?_⟩
      have : eval₂ (algebraMap ℤ L) α (X ^ n - X - 1 : ℤ[X]) = eval α fL := by
        simp [fL, eval₂_sub, eval₂_pow]
      rw [this, hroot]
    obtain ⟨a, ha⟩ : ∃ a : 𝓞 L, algebraMap (𝓞 L) L a = α := ⟨⟨α, hint⟩, rfl⟩
    refine Multiset.mem_map.mpr ⟨a, ?_, ha⟩
    rw [mem_roots hO0, IsRoot]
    apply hinj
    rw [← eval₂_hom, ← eval_map, hmap, ha, map_zero]
    exact hroot
  have hcard : n ≤ fO.roots.card := by
    have := Multiset.card_le_card ((Multiset.le_iff_subset hLnd).mpr hsub)
    rw [Multiset.card_map] at this
    omega
  refine ⟨splits_iff_card_roots.mpr (le_antisymm (card_roots' _) ?_), hOnd⟩
  rw [sn_natDegree n hn]; exact hcard

open Polynomial NumberField in
/-- S4: a number field in which no prime of `𝓞 E` is ramified over `ℤ` is `ℚ`. -/
lemma sn_unram {E : Type} [Field E] [NumberField E]
    (h : ∀ (Q : Ideal (𝓞 E)) [Q.IsMaximal], Algebra.IsUnramifiedAt ℤ Q) :
    Module.finrank ℚ E = 1 := by
  have hD : differentIdeal ℤ (𝓞 E) = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have hdvd : M ∣ differentIdeal ℤ (𝓞 E) := Ideal.dvd_iff_le.mpr hle
    have := h M
    exact (not_dvd_differentIdeal_iff.mpr this) hdvd
  have h1 : (discr E).natAbs = 1 := by
    rw [← absNorm_differentIdeal E (𝓞 E), hD, Ideal.absNorm_top]
  by_contra hne
  have hpos : 0 < Module.finrank ℚ E := Module.finrank_pos
  have := abs_discr_gt_two (K := E) (by omega)
  have : |discr E| = 1 := by
    rw [Int.abs_eq_natAbs, h1]; rfl
  linarith

open Polynomial NumberField in
lemma sn_card_inertia_sub {L : Type} [Field L] [NumberField L] (H : Subgroup Gal(L/ℚ))
    (P : Ideal (𝓞 L)) (hH : Ideal.inertia Gal(L/ℚ) P ≤ H) :
    Nat.card (Ideal.inertia H P) = Nat.card (Ideal.inertia Gal(L/ℚ) P) := by
  refine Nat.card_congr
    { toFun := fun σ => ⟨σ.1.1, Ideal.coe_mem_inertia.mpr σ.2⟩
      invFun := fun g => ⟨⟨g.1, hH g.2⟩, Ideal.coe_mem_inertia.mp g.2⟩
      left_inv := fun σ => rfl
      right_inv := fun g => rfl }

open Polynomial NumberField in
/-- S5: a subgroup containing every inertia group is everything (ℚ has no unramified extension). -/
lemma sn_gen {L : Type} [Field L] [NumberField L] [IsGalois ℚ L] (H : Subgroup Gal(L/ℚ))
    (hH : ∀ (P : Ideal (𝓞 L)), P.IsMaximal → Ideal.inertia Gal(L/ℚ) P ≤ H) : H = ⊤ := by
  set E := FixedPoints.intermediateField (F := ℚ) (E := L) H with hEdef
  haveI : IsGaloisGroup H (𝓞 E) (𝓞 L) := IsGaloisGroup.of_isFractionRing H (𝓞 E) (𝓞 L) E L
  have hE : Module.finrank ℚ E = 1 := by
    apply sn_unram
    intro Q _
    obtain ⟨⟨P, hPQ⟩⟩ := Ideal.nonempty_primesOver (S := 𝓞 L) Q
    haveI := hPQ.1
    haveI := hPQ.2
    have htow := Ideal.ramificationIdx_tower (R := ℤ) Q P
    have hG := Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(L/ℚ)) (P.under ℤ) P
    have hHc := Ideal.card_inertia_eq_ramificationIdxIn (G := H) Q P
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx (P.under ℤ) P Gal(L/ℚ)] at hG
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx Q P H] at hHc
    have hPmax : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P Q
    rw [sn_card_inertia_sub H P (hH P hPmax), hG] at hHc
    have hpos : 0 < P.ramificationIdx ℤ := by
      rw [← hG]; exact Nat.card_pos
    have h1 : Q.ramificationIdx ℤ = 1 := by
      rw [← hHc] at htow
      have := htow
      nlinarith [this]
    exact (Ideal.ramificationIdx_eq_one_iff).mp h1
  have hbot : E = ⊥ := IntermediateField.finrank_eq_one_iff.mp hE
  have := IntermediateField.fixingSubgroup_fixedField H
  rw [← this]
  show (IntermediateField.fixedField H).fixingSubgroup = ⊤
  rw [show IntermediateField.fixedField H = E from rfl, hbot, IntermediateField.fixingSubgroup_bot]

open Polynomial NumberField in
lemma sn_mem_rootSet_iff {L : Type} [Field L] [NumberField L] (n : ℕ) (hn : 2 ≤ n) (a : 𝓞 L) :
    a ∈ (X ^ n - X - 1 : ℤ[X]).rootSet (𝓞 L) ↔
      algebraMap (𝓞 L) L a ∈ (X ^ n - X - 1 : ℚ[X]).rootSet L := by
  have h1 : (X ^ n - X - 1 : ℤ[X]) ≠ 0 := (sn_monic n hn).ne_zero
  have h2 : (X ^ n - X - 1 : ℚ[X]) ≠ 0 := (sn_monic n hn).ne_zero
  have hinj : Function.Injective (algebraMap (𝓞 L) L) := FaithfulSMul.algebraMap_injective _ _
  simp only [mem_rootSet, ne_eq, h1, h2, not_false_eq_true, true_and, map_sub, map_pow,
    aeval_X, map_one]
  constructor
  · intro h
    have := congrArg (algebraMap (𝓞 L) L) h
    simpa using this
  · intro h
    apply hinj
    simpa using h

open Polynomial NumberField in
/-- S6: the Galois group of the splitting field of `Xⁿ - X - 1` acts as the full symmetric group
on the roots in `𝓞 L`. -/
lemma sn_bij (n : ℕ) (hn : 2 ≤ n) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : IsGalois ℚ L),
      Function.Bijective (MulAction.toPermHom Gal(L/ℚ) ((X ^ n - X - 1 : ℤ[X]).rootSet (𝓞 L))) ∧
      Nat.card ((X ^ n - X - 1 : ℤ[X]).rootSet (𝓞 L)) = n := by
  classical
  obtain ⟨fQ, hfQ⟩ : ∃ f : ℚ[X], f = X ^ n - X - 1 := ⟨_, rfl⟩
  have hirr : Irreducible fQ := hfQ ▸ X_pow_sub_X_sub_one_irreducible_rat (by omega)
  let L := fQ.SplittingField
  have hspl : IsSplittingField ℚ L fQ := by
    convert IsSplittingField.splittingField fQ
    exact Subsingleton.elim _ _
  have : IsGalois ℚ L := IsGalois.of_separable_splitting_field (p := fQ) hirr.separable
  letI : NumberField L := NumberField.of_module_finite ℚ L
  have hsL : (X ^ n - X - 1 : L[X]).Splits := by
    have := SplittingField.splits fQ
    simpa [hfQ] using this
  obtain ⟨hsO, hnd⟩ := sn_rootsO (L := L) n hn hsL
  haveI : Fact ((map (algebraMap ℚ L) fQ).Splits) := ⟨SplittingField.splits _⟩
  -- every root in `L` comes from a root in `𝓞 L`
  have hlift : ∀ α ∈ fQ.rootSet L, ∃ a : 𝓞 L, a ∈ (X ^ n - X - 1 : ℤ[X]).rootSet (𝓞 L) ∧
      algebraMap (𝓞 L) L a = α := by
    intro α hα
    have hroot : aeval α fQ = 0 := (mem_rootSet.mp hα).2
    have hint : IsIntegral ℤ α := by
      refine ⟨X ^ n - X - 1, sn_monic n hn, ?_⟩
      have : eval₂ (algebraMap ℤ L) α (X ^ n - X - 1 : ℤ[X]) = aeval α fQ := by
        simp [hfQ, eval₂_sub, eval₂_pow, aeval_def]
      rw [this, hroot]
    obtain ⟨a, ha⟩ : ∃ a : 𝓞 L, algebraMap (𝓞 L) L a = α := ⟨⟨α, hint⟩, rfl⟩
    exact ⟨a, (sn_mem_rootSet_iff n hn a).mpr (hfQ ▸ ha ▸ hα), ha⟩
  -- transitivity
  haveI hpt : MulAction.IsPretransitive Gal(L/ℚ) ((X ^ n - X - 1 : ℤ[X]).rootSet (𝓞 L)) := by
    refine ⟨fun x y => ?_⟩
    have hx := (sn_mem_rootSet_iff n hn x.1).mp x.2
    have hy := (sn_mem_rootSet_iff n hn y.1).mp y.2
    rw [← hfQ] at hx hy
    haveI := Gal.galAction_isPretransitive fQ L hirr
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq fQ.Gal (⟨_, hx⟩ : fQ.rootSet L) ⟨_, hy⟩
    obtain ⟨ϕ, rfl⟩ := Gal.restrict_surjective fQ L g
    refine ⟨ϕ, Subtype.ext ?_⟩
    apply FaithfulSMul.algebraMap_injective (𝓞 L) L
    have := Gal.restrict_smul ϕ (⟨_, hx⟩ : fQ.rootSet L)
    rw [hg] at this
    exact this.symm
  have hnd' : ((X ^ n - X - 1 : ℤ[X]).aroots (𝓞 L)).Nodup := by simpa [aroots] using hnd
  have hcardO : ((X ^ n - X - 1 : ℤ[X]).aroots (𝓞 L)).card = n := by
    have := splits_iff_card_roots.mp hsO
    rw [sn_natDegree n hn] at this
    simpa [aroots] using this
  have hncardO : ((X ^ n - X - 1 : ℤ[X]).rootSet (𝓞 L)).ncard = n := by
    rw [rootSet_def, Set.ncard_coe_finset, Multiset.toFinset_card_of_nodup hnd', hcardO]
  have hcond : ∀ m : MaximalSpectrum (𝓞 L), ((X ^ n - X - 1 : ℤ[X]).rootSet (𝓞 L)).ncard ≤
      ((X ^ n - X - 1 : ℤ[X]).rootSet (𝓞 L ⧸ m.asIdeal)).ncard + 1 := by
    intro m
    letI : Field (𝓞 L ⧸ m.asIdeal) := Ideal.Quotient.field _
    rw [hncardO, rootSet_def, Set.ncard_coe_finset]
    have hsk : (X ^ n - X - 1 : (𝓞 L ⧸ m.asIdeal)[X]).Splits := by
      have := hsO.map (Ideal.Quotient.mk m.asIdeal)
      simpa using this
    have := sn_res_count n hn hsk
    simpa [aroots] using this
  have hfsplit : (map (algebraMap ℤ (𝓞 L)) (X ^ n - X - 1 : ℤ[X])).Splits := by simpa using hsO
  have htop : (⨆ m : MaximalSpectrum (𝓞 L), Ideal.inertia Gal(L/ℚ) m.asIdeal) = ⊤ :=
    sn_gen _ (fun P hP => le_iSup_of_le (⟨P, hP⟩ : MaximalSpectrum (𝓞 L)) le_rfl)
  have hsurj := Polynomial.Splits.surjective_toPermHom_of_iSup_inertia_eq_top hfsplit hcond htop
  have hinj : Function.Injective
      (MulAction.toPermHom Gal(L/ℚ) ((X ^ n - X - 1 : ℤ[X]).rootSet (𝓞 L))) := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    have hfix : Set.EqOn (σ.toAlgHom : L →ₐ[ℚ] L) (AlgHom.id ℚ L) (fQ.rootSet L) := by
      intro α hα
      obtain ⟨a, ha, rfl⟩ := hlift α hα
      have := congrArg (fun p : Equiv.Perm ((X ^ n - X - 1 : ℤ[X]).rootSet (𝓞 L)) =>
        ((p ⟨a, ha⟩ : (X ^ n - X - 1 : ℤ[X]).rootSet (𝓞 L)) : 𝓞 L)) hσ
      simp only [MulAction.toPermHom_apply, MulAction.toPerm_apply, Equiv.Perm.coe_one, id] at this
      have h2 : algebraMap (𝓞 L) L (σ • a) = σ (algebraMap (𝓞 L) L a) := rfl
      simp only [AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, AlgHom.coe_id, id]
      exact h2.symm.trans (congrArg _ this)
    have := AlgHom.ext_of_adjoin_eq_top (SplittingField.adjoin_rootSet fQ) hfix
    ext x
    exact congrArg (fun φ : L →ₐ[ℚ] L => φ x) this
  refine ⟨L, inferInstance, inferInstance, inferInstance, ⟨hinj, hsurj⟩, ?_⟩
  rw [Nat.card_coe_set_eq, hncardO]

open Polynomial NumberField in
/-- `Gal(ℚ/ℚ)` is trivial. -/
noncomputable def snUniqueGalQ : Unique (ℚ ≃ₐ[ℚ] ℚ) where
  default := 1
  uniq σ := AlgEquiv.ext fun x => by simpa using σ.commutes x

/--
Every finite symmetric group is realizable.
-/
@[category research solved, AMS 12]
theorem inverse_galois_problem.variants.symmetric_group
    {S : Type*} [Fintype S] :
    IsRealizable ℚ (S ≃ S) := by
  classical
  by_cases h : Fintype.card S ≤ 1
  · haveI : Subsingleton S := Fintype.card_le_one_iff_subsingleton.mp h
    letI := snUniqueGalQ
    exact ⟨⟨⟨ℚ, inferInstance, inferInstance, inferInstance, MulEquiv.ofUnique⟩⟩⟩
  · obtain ⟨L, hF, hN, hG, hbij, hcard⟩ := sn_bij (Fintype.card S) (by omega)
    obtain ⟨e⟩ := Finite.card_eq.mp (hcard.trans (Nat.card_eq_fintype_card (α := S)).symm)
    exact ⟨⟨⟨L, hF, inferInstance, hG,
      (Equiv.permCongrHom e.symm).trans (MulEquiv.ofBijective _ hbij).symm⟩⟩⟩


/--
Every finite group is realisable over the field of rational functions
with complex coefficients.
-/
@[category research solved, AMS 12]
theorem inverse_galois_problem.variants.complex_rational_functions
    {G : Type*} [Fintype G] [Group G] :
    IsRealizable (RatFunc ℂ) G := by
  sorry

/--
Every finite group is realisable over the field of rational functions
with coefficients `K`, where `K` is any algebraically closed field of characteristic 0.
-/
@[category research solved, AMS 12]
theorem inverse_galois_problem.variants.complex_function_field
    {G K : Type*} [Field K] [IsAlgClosed K] [CharZero K] [Fintype G] [Group G] :
    IsRealizable (RatFunc K) G := by
  sorry

end InverseGalois
