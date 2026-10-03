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
# Erdős Problem 723: The prime power conjecture.

*Reference:* [erdosproblems.com/723](https://www.erdosproblems.com/723)
-/

@[expose] public section

open Configuration

namespace Erdos723

/--
If there is a finite projective plane of order $n$ then must $n$ be a prime power?
-/
@[category research open, AMS 5]
theorem erdos_723 :
    answer(sorry) ↔ ∀ {P L : Type} (_: Membership P L) (_ : Fintype P) (_ : Fintype L),
      ∀ pp : ProjectivePlane P L, IsPrimePow pp.order := by
  sorry

open Configuration in
lemma pp_order_eq (K : Type) [Field K] [Fintype K] [DecidableEq K]
    [Fintype (Projectivization K (Fin 3 → K))] :
    ProjectivePlane.order (Projectivization K (Fin 3 → K)) (Projectivization K (Fin 3 → K)) =
      Fintype.card K := by
  set P := Projectivization K (Fin 3 → K)
  set o := ProjectivePlane.order P P
  set q := Fintype.card K with hq
  have h1 := ProjectivePlane.card_points P P
  have h2 := Projectivization.card' K (Fin 3 → K)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h2
  simp only [Fintype.card_fun, Fintype.card_fin] at h2
  rw [← hq] at h2
  have hq2 : 2 ≤ q := by
    have := Fintype.one_lt_card (α := K); omega
  have hP : Fintype.card P = q ^ 2 + q + 1 := by
    have e : q ^ 3 = (q ^ 2 + q + 1) * (q - 1) + 1 := by
      obtain ⟨r, hr⟩ : ∃ r, q = r + 2 := ⟨q - 2, by omega⟩
      rw [hr, show r + 2 - 1 = r + 1 by omega]; ring
    rw [e] at h2
    have hq1 : 0 < q - 1 := by omega
    exact (Nat.eq_of_mul_eq_mul_right hq1 (Nat.add_right_cancel h2)).symm
  rw [hP] at h1
  rcases lt_trichotomy o q with h | h | h
  · nlinarith
  · exact h
  · nlinarith

/--
These always exist if $n$ is a prime power.
-/
@[category research solved, AMS 5]
theorem erdos_723.variants.prime_power_is_projplane_order :
    ∀ n, IsPrimePow n → ∃ (P L : Type) (_ : Membership P L) (_ : Fintype P) (_ : Fintype L)
      (pp : ProjectivePlane P L), pp.order = n := by
  intro n hn
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hn
  have : Fact p.Prime := ⟨hp⟩
  classical
  let K := GaloisField p k
  let _ : Fintype K := Fintype.ofFinite K
  let _ : Fintype (Projectivization K (Fin 3 → K)) := Fintype.ofFinite _
  refine ⟨Projectivization K (Fin 3 → K), Projectivization K (Fin 3 → K), inferInstance,
    inferInstance, inferInstance, inferInstance, ?_⟩
  rw [pp_order_eq K, ← Nat.card_eq_fintype_card]
  exact GaloisField.card p k hk.ne'

/--
This conjecture has been proved for $n \leq 11$.
-/
@[category research solved, AMS 5]
theorem erdos_723.variants.leq_11 {P L : Type} [Membership P L] [Fintype P] [Fintype L] :
    ∀ pp : ProjectivePlane P L, pp.order ≤ 11 → IsPrimePow pp.order := by
  sorry

/--
It is open whether there exists a projective plane of order 12.
-/
@[category research open, AMS 5]
theorem erdos_723.variants.eq_12 : answer(sorry) ↔
    ∃ (P L : Type) (_ : Membership P L) (_ : Fintype P) (_ : Fintype L) (pp : ProjectivePlane P L),
      pp.order = 12 := by
  sorry

/--
Bruck and Ryser have proved that if $n \equiv 1 (\mod 4)$ or $n \equiv 2 (\mod 4)$ then $n$ must be
the sum of two squares.
-/
@[category research solved, AMS 5]
theorem erdos_723.variants.bruck_ryser {P L : Type} [Membership P L] [Fintype P] [Fintype L]
    (n : ℕ) (pp : ProjectivePlane P L) (hpp : pp.order = n) :
    (n ≡ 1 [MOD 4] ∨ n ≡ 2 [MOD 4]) → ∃ a b, n = a ^ 2 + b ^ 2 := by
  sorry

end Erdos723
