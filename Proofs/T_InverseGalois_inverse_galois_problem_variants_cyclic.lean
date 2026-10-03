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

/-- IG2: a quotient of `(ZMod N)ˣ` is realizable over `ℚ`. -/
lemma ig_realize {G : Type*} [CommGroup G] (N : ℕ) [NeZero N] (φ : (ZMod N)ˣ →* G)
    (hφ : Function.Surjective φ) : IsRealizable ℚ G := by
  let K := CyclotomicField N ℚ
  have hirr : Irreducible (Polynomial.cyclotomic N ℚ) :=
    Polynomial.cyclotomic.irreducible_rat (Nat.pos_of_ne_zero (NeZero.ne N))
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  haveI : IsCyclotomicExtension {N} ℚ K := CyclotomicField.isCyclotomicExtension N ℚ
  haveI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {N} ℚ K
  haveI : FiniteDimensional ℚ K := IsCyclotomicExtension.finiteDimensional {N} ℚ K
  let σ : (K ≃ₐ[ℚ] K) ≃* (ZMod N)ˣ := IsCyclotomicExtension.autEquivPow K hirr
  let ψ : (K ≃ₐ[ℚ] K) →* G := φ.comp σ.toMonoidHom
  have hψ : Function.Surjective ψ := hφ.comp σ.surjective
  let H := ψ.ker
  let F := IntermediateField.fixedField H
  have e : G ≃* (F ≃ₐ[ℚ] F) :=
    ((IsGalois.normalAutEquivQuotient H).symm.trans (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)).symm
  exact ⟨⟨⟨F, inferInstance, inferInstance, IsGalois.of_fixedField_normal_subgroup H, e⟩⟩⟩

/-- IG1a: injectively many primes `≡ 1 (mod M)`. -/
lemma ig_primes (ι : Type*) [Fintype ι] (M : ℕ) [NeZero M] :
    ∃ p : ι → ℕ, Function.Injective p ∧ ∀ i, (p i).Prime ∧ ((p i : ZMod M) = 1) := by
  let S : Set ℕ := {p | p.Prime ∧ (p : ZMod M) = 1}
  have hS : S.Infinite := by
    apply Set.infinite_of_forall_exists_gt
    intro a
    obtain ⟨p, hpa, hp, hp1⟩ := Nat.forall_exists_prime_gt_and_eq_mod (q := M) (a := 1) isUnit_one a
    exact ⟨p, ⟨hp, hp1⟩, hpa⟩
  let emb := hS.natEmbedding
  refine ⟨fun i => (emb (Fintype.equivFin ι i)).1, ?_, fun i => (emb (Fintype.equivFin ι i)).2⟩
  intro i j h
  have := emb.injective (Subtype.val_injective h)
  exact (Fintype.equivFin ι).injective (Fin.val_injective this)

/-- IG1b: `(ZMod p)ˣ` surjects onto `ZMod n` when `n ∣ p - 1`. -/
lemma ig_cyc (p n : ℕ) [Fact p.Prime] (h : n ∣ p - 1) :
    ∃ f : (ZMod p)ˣ →* Multiplicative (ZMod n), Function.Surjective f := by
  have hcyc : IsCyclic (ZMod p)ˣ := inferInstance
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units p]
  have h' : n ∣ Nat.card (ZMod p)ˣ := hcard ▸ h
  let e := zmodCyclicMulEquiv hcyc
  let g : Multiplicative (ZMod (Nat.card (ZMod p)ˣ)) →* Multiplicative (ZMod n) :=
    AddMonoidHom.toMultiplicative (ZMod.castHom h' (ZMod n)).toAddMonoidHom
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x, hx⟩ := ZMod.castHom_surjective h' (Multiplicative.toAdd y)
    refine ⟨Multiplicative.ofAdd x, ?_⟩
    simp only [g, AddMonoidHom.toMultiplicative_apply_apply, toAdd_ofAdd]
    rw [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, hx, ofAdd_toAdd]
  refine ⟨g.comp e.symm.toMonoidHom, ?_⟩
  rw [MonoidHom.coe_comp]
  exact hg.comp e.symm.surjective

/-- IG1: every finite abelian group is a quotient of some `(ZMod N)ˣ`. -/
lemma ig_quotient (G : Type*) [CommGroup G] [Finite G] :
    ∃ N : ℕ, ∃ _ : NeZero N, ∃ φ : (ZMod N)ˣ →* G, Function.Surjective φ := by
  obtain ⟨ι, hι, n, hn, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite G
  set M := ∏ i, n i with hM
  haveI : NeZero M := ⟨Finset.prod_ne_zero_iff.mpr fun i _ => by have := hn i; omega⟩
  obtain ⟨p, hpinj, hp⟩ := ig_primes ι M
  haveI : ∀ i, Fact (p i).Prime := fun i => ⟨(hp i).1⟩
  have hdvd : ∀ i, n i ∣ p i - 1 := by
    intro i
    have h1 : (p i : ZMod M) = ((1 : ℕ) : ZMod M) := by rw [(hp i).2]; simp
    rw [ZMod.natCast_eq_natCast_iff] at h1
    have h2 : M ∣ p i - 1 := (Nat.modEq_iff_dvd' (hp i).1.one_le).mp h1.symm
    exact (Finset.dvd_prod_of_mem n (Finset.mem_univ i)).trans h2
  have hcop : Pairwise (Function.onFun Nat.Coprime p) := by
    intro i j hij
    exact (Nat.coprime_primes (hp i).1 (hp j).1).mpr (hpinj.ne hij)
  set N := ∏ i, p i with hN
  haveI : NeZero N := ⟨Finset.prod_ne_zero_iff.mpr fun i _ => (hp i).1.ne_zero⟩
  let crt : ZMod N ≃+* Π i, ZMod (p i) := ZMod.prodEquivPi p hcop
  let u : (ZMod N)ˣ ≃* Π i, (ZMod (p i))ˣ :=
    (Units.mapEquiv crt.toMulEquiv).trans MulEquiv.piUnits
  choose f hf using fun i => ig_cyc (p i) (n i) (hdvd i)
  let F : (Π i, (ZMod (p i))ˣ) →* (Π i, Multiplicative (ZMod (n i))) :=
    Pi.monoidHom (fun i => (f i).comp (Pi.evalMonoidHom _ i))
  have hF : Function.Surjective F := by
    intro y
    refine ⟨fun i => (hf i (y i)).choose, funext fun i => ?_⟩
    simp only [F, Pi.monoidHom_apply, MonoidHom.coe_comp, Function.comp_apply, Pi.evalMonoidHom_apply]
    exact (hf i (y i)).choose_spec
  refine ⟨N, inferInstance, e.symm.toMonoidHom.comp (F.comp u.toMonoidHom), ?_⟩
  exact e.symm.surjective.comp (hF.comp u.surjective)

theorem ig_abelian {G : Type*} [Fintype G] [CommGroup G] : IsRealizable ℚ G := by
  obtain ⟨N, hN, φ, hφ⟩ := ig_quotient G
  exact ig_realize N φ hφ

theorem ig_cyclic {G : Type*} [Fintype G] [Group G] [IsCyclic G] : IsRealizable ℚ G := by
  letI : CommGroup G := IsCyclic.commGroup
  exact ig_abelian

/--
Every finite cyclic group is realizable.
-/
@[category research solved, AMS 12]
theorem inverse_galois_problem.variants.cyclic
    {G : Type*} [Fintype G] [Group G] [IsCyclic G] :
    IsRealizable ℚ G := by
  exact ig_cyclic

/--
Every finite abelian group is realizable.
-/
@[category research solved, AMS 12]
theorem inverse_galois_problem.variants.abelian
    {G : Type*} [Fintype G] [CommGroup G] :
    IsRealizable ℚ G := by
  sorry

/--
Every finite symmetric group is realizable.
-/
@[category research solved, AMS 12]
theorem inverse_galois_problem.variants.symmetric_group
    {S : Type*} [Fintype S] :
    IsRealizable ℚ (S ≃ S) := by
  sorry

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
