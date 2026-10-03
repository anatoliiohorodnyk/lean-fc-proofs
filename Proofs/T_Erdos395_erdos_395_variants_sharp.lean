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
# Erdős Problem 395

*References:*
- [erdosproblems.com/395](https://www.erdosproblems.com/395)
- [Er45] Erdős, P., *On a lemma of Littlewood and Offord*. Bull. Amer. Math. Soc. (1945),
  898--902.
- [CaCa11] Carnielli, Walter and Carolino, Pietro K., *Adjusting a conjecture of Erdős*. Contrib.
  Discrete Math. (2011), 154--159.
- [HJNS24] X. He, T. Juškevičius, B. Narayanan, and S. Spiro, *The Reverse Littlewood-Offord
  problem of Erdős*. arXiv:2408.11034 (2024).
-/

@[expose] public section

namespace Erdos395

/-- The number of sign patterns $\epsilon \in \{-1,1\}^n$ with
$\lvert \epsilon_1z_1+\cdots+\epsilon_nz_n\rvert \leq r$. -/
noncomputable def signedSumCount {n : ℕ} (z : Fin n → ℂ) (r : ℝ) : ℕ :=
  {ε : Fin n → ℤ | (∀ i, ε i = -1 ∨ ε i = 1) ∧ ‖∑ i, (ε i : ℂ) * z i‖ ≤ r}.ncard

/--
If $z_1,\ldots,z_n\in \mathbb{C}$ with $\lvert z_i\rvert=1$ then is it true that the probability
that
$$\lvert \epsilon_1z_1+\cdots+\epsilon_nz_n\rvert \leq \sqrt{2},$$
where $\epsilon_i\in \{-1,1\}$ uniformly at random, is $\gg 1/n$?

A reverse Littlewood-Offord problem. Erdős originally asked this with $\sqrt{2}$ replaced by $1$,
but Carnielli and Carolino [CaCa11] observed that this is false, choosing $z_1=1$ and $z_k=i$
for $2\leq k\leq n$, where $n$ is even, since then the sum is at least $\sqrt{2}$ always.

Solved in the affirmative by He, Juškevičius, Narayanan, and Spiro [HJNS24]. The bound of $1/n$
is the best possible, as shown by taking $z_k=1$ for $1\leq k\leq n/2$ and $z_k=i$ otherwise.

See also [498](https://www.erdosproblems.com/498).
-/
@[category research solved, AMS 5 60, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos395.lean#L4058"]
theorem erdos_395 : answer(True) ↔ ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n → ∀ z : Fin n → ℂ,
    (∀ i, ‖z i‖ = 1) → c / n ≤ (signedSumCount z √2 : ℝ) / 2 ^ n := by
  sorry

/--
Erdős originally asked [erdős_395](https://www.erdosproblems.com/395) with $\sqrt{2}$ replaced by
$1$, but Carnielli and Carolino [CaCa11] observed that this is false, choosing $z_1=1$ and $z_k=i$
for $2\leq k\leq n$, where $n$ is even, since then the sum is at least $\sqrt{2}$ always.
-/
@[category research solved, AMS 5 60]
theorem erdos_395.variants.one : answer(False) ↔ ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n →
    ∀ z : Fin n → ℂ, (∀ i, ‖z i‖ = 1) → c / n ≤ (signedSumCount z 1 : ℝ) / 2 ^ n := by
  sorry

lemma e395_cb (k : ℕ) : k.centralBinom ^ 2 * (3 * k + 1) ≤ 16 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hrec := Nat.succ_mul_centralBinom_succ k
    -- (k+1)^2 * cb(k+1)^2 * (3k+4) = 4(2k+1)^2 cb(k)^2 (3k+4) ≤ 16 (k+1)^2 cb(k)^2 (3k+1)
    have key : (k + 1) ^ 2 * ((k + 1).centralBinom ^ 2 * (3 * (k + 1) + 1))
        ≤ (k + 1) ^ 2 * 16 ^ (k + 1) := by
      have e1 : (k + 1) ^ 2 * ((k + 1).centralBinom ^ 2 * (3 * (k + 1) + 1))
          = (2 * (2 * k + 1)) ^ 2 * k.centralBinom ^ 2 * (3 * k + 4) := by
        have : ((k + 1) * (k + 1).centralBinom) ^ 2 = (2 * (2 * k + 1) * k.centralBinom) ^ 2 := by
          rw [hrec]
        nlinarith [this]
      have e2 : (2 * (2 * k + 1)) ^ 2 * (3 * k + 4) ≤ 16 * ((k + 1) ^ 2 * (3 * k + 1)) := by
        nlinarith
      rw [e1, pow_succ]
      calc (2 * (2 * k + 1)) ^ 2 * k.centralBinom ^ 2 * (3 * k + 4)
          = ((2 * (2 * k + 1)) ^ 2 * (3 * k + 4)) * k.centralBinom ^ 2 := by ring
        _ ≤ (16 * ((k + 1) ^ 2 * (3 * k + 1))) * k.centralBinom ^ 2 := Nat.mul_le_mul_right _ e2
        _ = (k + 1) ^ 2 * 16 * (k.centralBinom ^ 2 * (3 * k + 1)) := by ring
        _ ≤ (k + 1) ^ 2 * 16 * 16 ^ k := Nat.mul_le_mul_left _ ih
        _ = (k + 1) ^ 2 * (16 ^ k * 16) := by ring
    exact Nat.le_of_mul_le_mul_left key (by positivity)

/-- `C(m, ⌊m/2⌋)² · (m + 1) ≤ 2 · 4^m`. -/
lemma e395_half (m : ℕ) : (m.choose (m / 2)) ^ 2 * (m + 1) ≤ 2 * 4 ^ m := by
  rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
  · have h := e395_cb k
    rw [Nat.centralBinom_eq_two_mul_choose] at h
    rw [show 2 * k / 2 = k by omega]
    have : 4 ^ (2 * k) = 16 ^ k := by rw [pow_mul]; norm_num
    rw [this]
    calc ((2 * k).choose k) ^ 2 * (2 * k + 1) ≤ ((2 * k).choose k) ^ 2 * (3 * k + 1) :=
          Nat.mul_le_mul_left _ (by omega)
      _ ≤ 16 ^ k := h
      _ ≤ 2 * 16 ^ k := by omega
  · have h := e395_cb (k + 1)
    rw [Nat.centralBinom_eq_two_mul_choose] at h
    rw [show (2 * k + 1) / 2 = k by omega]
    have hc : (2 * (k + 1)).choose (k + 1) = 2 * (2 * k + 1).choose k := by
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, Nat.choose_succ_succ, Nat.succ_eq_add_one,
        Nat.choose_symm_half]
      ring
    rw [hc] at h
    have : 4 ^ (2 * k + 1) = 4 * 16 ^ k := by rw [pow_succ, pow_mul]; norm_num; ring
    rw [this]
    have h16 : 16 ^ (k + 1) = 16 * 16 ^ k := by ring
    rw [h16] at h
    nlinarith

lemma e395_sum_pm {ι : Type*} (F : Finset ι) (ε : ι → ℤ) (h : ∀ i ∈ F, ε i = -1 ∨ ε i = 1) :
    ∑ i ∈ F, ε i = 2 * ((F.filter (fun i => ε i = 1)).card : ℤ) - F.card := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not F (fun i => ε i = 1)]
  have h1 : ∑ i ∈ F.filter (fun i => ε i = 1), ε i = (F.filter (fun i => ε i = 1)).card := by
    rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2)]; simp
  have h2 : ∑ i ∈ F.filter (fun i => ¬ ε i = 1), ε i = -((F.filter (fun i => ¬ ε i = 1)).card : ℤ) := by
    rw [Finset.sum_congr rfl (fun i hi => (show ε i = -1 by
      obtain ⟨hF, hne⟩ := Finset.mem_filter.mp hi; rcases h i hF with h' | h'
      · exact h'
      · exact absurd h' hne))]
    simp
  have h3 := Finset.card_filter_add_card_filter_not (s := F) (fun i => ε i = 1)
  rw [h1, h2]
  have : ((F.filter (fun i => ¬ ε i = 1)).card : ℤ) = F.card - (F.filter (fun i => ε i = 1)).card := by
    rw [← h3]; push_cast; ring
  rw [this]; ring

/-- Subsets of `ι` with prescribed intersection sizes with `F` and `Fᶜ`. -/
lemma e395_count {ι : Type*} [Fintype ι] [DecidableEq ι] (F : Finset ι) (a b : ℕ) :
    ((Finset.univ : Finset (Finset ι)).filter
      (fun P => (P ∩ F).card = a ∧ (P ∩ Fᶜ).card = b)).card
      ≤ F.card.choose a * Fᶜ.card.choose b := by
  rw [← Finset.card_powersetCard a F, ← Finset.card_powersetCard b Fᶜ, ← Finset.card_product]
  refine Finset.card_le_card_of_injOn (fun P => (P ∩ F, P ∩ Fᶜ)) ?_ ?_
  · intro P hP
    obtain ⟨-, ha, hb⟩ := Finset.mem_filter.mp hP
    exact Finset.mem_product.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right, ha⟩,
      Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right, hb⟩⟩
  · intro P _ Q _ h
    simp only [Prod.mk.injEq] at h
    ext x
    by_cases hx : x ∈ F
    · have := congrArg (x ∈ ·) h.1; simpa [hx] using this
    · have := congrArg (x ∈ ·) h.2; simpa [hx] using this


set_option maxHeartbeats 1000000 in
/-- The key counting bound for the half-`1`, half-`i` configuration. -/
lemma e395_main_count (n : ℕ) (hn : 0 < n) :
    ∃ z : Fin n → ℂ, (∀ i, ‖z i‖ = 1) ∧ n * signedSumCount z √2 ≤ 16 * 2 ^ n := by
  classical
  set m := n / 2 with hm
  set F : Finset (Fin n) := Finset.univ.filter (fun i => i.val < m) with hF
  have hFc : F.card = m := by
    rw [hF, Fin.card_filter_val_lt]; omega
  have hFcc : Fᶜ.card = n - m := by rw [Finset.card_compl, hFc, Fintype.card_fin]
  set r := n - m with hr
  set z : Fin n → ℂ := fun i => if i ∈ F then 1 else Complex.I with hz
  refine ⟨z, fun i => by simp only [hz]; split_ifs <;> simp, ?_⟩
  set S := {ε : Fin n → ℤ | (∀ i, ε i = -1 ∨ ε i = 1) ∧ ‖∑ i, (ε i : ℂ) * z i‖ ≤ √2} with hS
  set X := m.choose (m / 2)
  set Y := r.choose (r / 2)
  -- constraint: each half-sum is in {-1, 0, 1}
  have hcons : ∀ ε ∈ S, (2 * ((F.filter (fun i => ε i = 1)).card : ℤ) - m) ^ 2 ≤ 1 ∧
      (2 * ((Fᶜ.filter (fun i => ε i = 1)).card : ℤ) - r) ^ 2 ≤ 1 := by
    rintro ε ⟨hpm, hnorm⟩
    have h1 := e395_sum_pm F ε (fun i _ => hpm i)
    have h2 := e395_sum_pm Fᶜ ε (fun i _ => hpm i)
    rw [hFc] at h1; rw [hFcc] at h2
    set S1 := ∑ i ∈ F, ε i
    set S2 := ∑ i ∈ Fᶜ, ε i
    have hsum : ∑ i, (ε i : ℂ) * z i = ((S1 : ℝ) : ℂ) + ((S2 : ℝ) : ℂ) * Complex.I := by
      rw [← Finset.sum_add_sum_compl F]
      simp only [hz, S1, S2]
      congr 1
      · rw [Finset.sum_congr rfl (fun i hi => by rw [if_pos hi, mul_one])]; push_cast; rfl
      · rw [Finset.sum_congr rfl (fun i hi => by rw [if_neg (Finset.mem_compl.mp hi)]),
          ← Finset.sum_mul]; push_cast; rfl
    rw [hsum, Complex.norm_def, Complex.normSq_add_mul_I] at hnorm
    have hsq : (S1 : ℝ) ^ 2 + (S2 : ℝ) ^ 2 ≤ 2 := by
      have := Real.sqrt_le_sqrt_iff (by positivity) |>.mp hnorm
      linarith
    have a1 : (S1 : ℝ) ^ 2 ≤ 2 := by nlinarith
    have a2 : (S2 : ℝ) ^ 2 ≤ 2 := by nlinarith
    have b1 : S1 ^ 2 ≤ 2 := by exact_mod_cast a1
    have b2 : S2 ^ 2 ≤ 2 := by exact_mod_cast a2
    rw [← h1, ← h2]
    have c1 : S1 ≤ 1 := by by_contra h; push Not at h; nlinarith
    have c2 : -1 ≤ S1 := by by_contra h; push Not at h; nlinarith
    have c3 : S2 ≤ 1 := by by_contra h; push Not at h; nlinarith
    have c4 : -1 ≤ S2 := by by_contra h; push Not at h; nlinarith
    constructor <;> nlinarith
  -- the injection into subsets with prescribed intersection sizes
  set φ : (Fin n → ℤ) → Finset (Fin n) := fun ε => Finset.univ.filter (fun i => ε i = 1) with hφ
  set A2 : Finset ℕ := {m / 2, (m + 1) / 2}
  set B2 : Finset ℕ := {r / 2, (r + 1) / 2}
  set U : Finset (Finset (Fin n)) := (A2 ×ˢ B2).biUnion (fun ab => Finset.univ.filter
    (fun P => (P ∩ F).card = ab.1 ∧ (P ∩ Fᶜ).card = ab.2)) with hU
  have hsq_to : ∀ (a k : ℕ), (2 * (a : ℤ) - k) ^ 2 ≤ 1 → a = k / 2 ∨ a = (k + 1) / 2 := by
    intro a k h
    have h1 : 2 * (a : ℤ) - k ≤ 1 := by by_contra h'; push Not at h'; nlinarith
    have h2 : -1 ≤ 2 * (a : ℤ) - k := by by_contra h'; push Not at h'; nlinarith
    omega
  have hinter : ∀ ε (G : Finset (Fin n)), φ ε ∩ G = G.filter (fun i => ε i = 1) := by
    intro ε G; ext i; simp [hφ, and_comm]
  have hmaps : ∀ ε ∈ S, φ ε ∈ (U : Set (Finset (Fin n))) := by
    intro ε hε
    obtain ⟨c1, c2⟩ := hcons ε hε
    rw [Finset.mem_coe, hU, Finset.mem_biUnion]
    refine ⟨((F.filter (fun i => ε i = 1)).card, (Fᶜ.filter (fun i => ε i = 1)).card), ?_, ?_⟩
    · rw [Finset.mem_product]
      constructor
      · rcases hsq_to _ _ c1 with h | h <;> simp [A2, h]
      · rcases hsq_to _ _ c2 with h | h <;> simp [B2, h]
    · rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, by rw [hinter], by rw [hinter]⟩
  have hinj : Set.InjOn φ S := by
    intro ε hε ε' hε' h
    funext i
    have hi := congrArg (i ∈ ·) h
    simp only [hφ, Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff] at hi
    rcases hε.1 i with h1 | h1 <;> rcases hε'.1 i with h2 | h2
    · rw [h1, h2]
    · exfalso; rw [h1, h2] at hi; norm_num at hi
    · exfalso; rw [h1, h2] at hi; norm_num at hi
    · rw [h1, h2]
  have hcardS : S.ncard ≤ U.card := by
    have := Set.ncard_le_ncard_of_injOn φ hmaps hinj (Finset.finite_toSet U)
    rwa [Set.ncard_coe_finset] at this
  have hcardU : U.card ≤ 4 * (X * Y) := by
    refine Finset.card_biUnion_le.trans ?_
    calc ∑ ab ∈ A2 ×ˢ B2, (Finset.univ.filter
            (fun P : Finset (Fin n) => (P ∩ F).card = ab.1 ∧ (P ∩ Fᶜ).card = ab.2)).card
        ≤ ∑ _ab ∈ A2 ×ˢ B2, X * Y := by
          refine Finset.sum_le_sum (fun ab _ => (e395_count F ab.1 ab.2).trans ?_)
          rw [hFc, hFcc]
          exact Nat.mul_le_mul (Nat.choose_le_middle _ _) (Nat.choose_le_middle _ _)
      _ = (A2 ×ˢ B2).card * (X * Y) := by simp
      _ ≤ 4 * (X * Y) := by
          apply Nat.mul_le_mul_right
          rw [Finset.card_product]
          have ha : A2.card ≤ 2 := Finset.card_le_two
          have hb : B2.card ≤ 2 := Finset.card_le_two
          nlinarith
  have hX := e395_half m
  have hY := e395_half r
  have hmr : m + r = n := by omega
  have hprod : (X * Y) ^ 2 * ((m + 1) * (r + 1)) ≤ 4 * 4 ^ n := by
    calc (X * Y) ^ 2 * ((m + 1) * (r + 1)) = (X ^ 2 * (m + 1)) * (Y ^ 2 * (r + 1)) := by ring
      _ ≤ (2 * 4 ^ m) * (2 * 4 ^ r) := Nat.mul_le_mul hX hY
      _ = 4 * 4 ^ n := by rw [← hmr, pow_add]; ring
  have hn2 : n ^ 2 ≤ 4 * ((m + 1) * (r + 1)) := by
    have : n ≤ 2 * m + 1 := by omega
    have : n ≤ 2 * r := by omega
    nlinarith
  have hkey : (n * (X * Y)) ^ 2 ≤ (4 * 2 ^ n) ^ 2 := by
    calc (n * (X * Y)) ^ 2 = n ^ 2 * (X * Y) ^ 2 := by ring
      _ ≤ 4 * ((m + 1) * (r + 1)) * (X * Y) ^ 2 := Nat.mul_le_mul_right _ hn2
      _ = 4 * ((X * Y) ^ 2 * ((m + 1) * (r + 1))) := by ring
      _ ≤ 4 * (4 * 4 ^ n) := Nat.mul_le_mul_left _ hprod
      _ = (4 * 2 ^ n) ^ 2 := by rw [show (4 : ℕ) ^ n = (2 ^ n) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]; ring
  have hkey' : n * (X * Y) ≤ 4 * 2 ^ n := (Nat.pow_le_pow_iff_left (by norm_num)).mp hkey
  calc n * signedSumCount z √2 = n * S.ncard := rfl
    _ ≤ n * (4 * (X * Y)) := Nat.mul_le_mul_left _ (hcardS.trans hcardU)
    _ = 4 * (n * (X * Y)) := by ring
    _ ≤ 4 * (4 * 2 ^ n) := Nat.mul_le_mul_left _ hkey'
    _ = 16 * 2 ^ n := by ring

/--
The bound of $1/n$ in [erdős_395](https://www.erdosproblems.com/395) is the best possible, as
shown by taking $z_k=1$ for $1\leq k\leq n/2$ and $z_k=i$ otherwise.
-/
@[category research solved, AMS 5 60]
theorem erdos_395.variants.sharp : ∃ C : ℝ, ∀ n : ℕ, 0 < n → ∃ z : Fin n → ℂ,
    (∀ i, ‖z i‖ = 1) ∧ (signedSumCount z √2 : ℝ) / 2 ^ n ≤ C / n := by
  refine ⟨16, fun n hn => ?_⟩
  obtain ⟨z, hz, hc⟩ := e395_main_count n hn
  refine ⟨z, hz, ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_div_iff₀ (by positivity) hnR]
  have : ((n * signedSumCount z √2 : ℕ) : ℝ) ≤ ((16 * 2 ^ n : ℕ) : ℝ) := by exact_mod_cast hc
  push_cast at this
  linarith

end Erdos395
