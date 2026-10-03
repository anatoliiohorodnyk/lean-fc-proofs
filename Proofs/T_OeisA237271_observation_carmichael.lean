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
# Number of parts in the symmetric representation of $\sigma(n)$

Number of parts in the symmetric representation of $\sigma(n)$. $a(n)$ is $1$ plus the number of pairs $(d_k, d_{k+1})$ of consecutive divisors of $n$
such that $d_{k+1}$ is odd and $d_{k+1} \ge 2 d_k$.

The formula used is
$1 + |\{(d_k, d_{k+1}) \in \text{consecutive pairs of divisors of } n \mid
d_{k+1} \text{ is odd and } d_{k+1} \ge 2 d_k\}|$,
which is a known characterization of the sequence.

*References:*
- [A237271](https://oeis.org/A237271)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/

@[expose] public section

namespace OeisA237271


open Nat Finset List

/--
Number of parts in the symmetric representation of $\sigma(n)$. $a(n)$ is $1$ plus the number of pairs $(d_k, d_{k+1})$ of consecutive divisors of $n$
such that $d_{k+1}$ is odd and $d_{k+1} \ge 2 d_k$.

The formula used is
$1 + |\{(d_k, d_{k+1}) \in \text{consecutive pairs of divisors of } n \mid
d_{k+1} \text{ is odd and } d_{k+1} \ge 2 d_k\}|$,
which is a known characterization of the sequence.
-/
def a (n : ℕ) : ℕ :=
  -- Get the list of divisors of n, sorted ascendingly.
  let divs_list : List ℕ := (n.divisors.sort (· ≤ ·))

  -- Get the list of consecutive pairs of divisors: [(d₁, d₂), (d₂, d₃), ...]
  let consecutive_pairs : List (ℕ × ℕ) := List.zip divs_list divs_list.tail

  -- Count the pairs satisfying the condition
  let count : ℕ := consecutive_pairs.countP fun pair =>
    let d_k := pair.fst
    let d_k_succ := pair.snd
    -- The second divisor d_{k+1} must be odd and at least twice the first divisor d_k.
    Odd d_k_succ ∧ d_k_succ ≥ 2 * d_k

  -- The sequence value is 1 + the count
  1 + count

def sortedDivisorsList (n : ℕ) : List ℕ := (n.divisors.sort (· ≤ ·))

/--
Number of maximal contiguous sublists of divisors of n where each adjacent pair (d_k, d_{k+1})
satisfies d_{k+1} <= 2 * d_k.
This is 1 + the number of "jumps" where d_{k+1} > 2 * d_k.
-/
def num2DenseSublists (n : ℕ) : ℕ :=
  let divs_list := sortedDivisorsList n
  let consecutive_pairs : List (ℕ × ℕ) := List.zip divs_list divs_list.tail

  -- A jump/break occurs when d_{k+1} > 2 * d_k
  let num_jumps : ℕ := consecutive_pairs.countP fun pair =>
    let d_k := pair.fst
    let d_k_succ := pair.snd
    d_k_succ > 2 * d_k

  1 + num_jumps


@[category test, AMS 11]
lemma a_1 : a 1 = 1 := by native_decide

@[category test, AMS 11]
lemma a_2 : a 2 = 1 := by native_decide

@[category test, AMS 11]
lemma a_3 : a 3 = 2 := by native_decide

@[category test, AMS 11]
lemma a_4 : a 4 = 1 := by native_decide

@[category test, AMS 11]
lemma a_5 : a 5 = 2 := by native_decide


/--
Conjecture 2: "a(n) is the number of 2-dense sublists of divisors of n.
We call '2-dense sublists of divisors of n' to the maximal sublists of divisors of n whose terms
increase by a factor of at most 2." - _Omar E. Pol_, Jul 31 2025

A formal proof has been found with the methods described in
[arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/237271.wip.lean#L102"]
theorem conjecture_2 (n : ℕ) : a n = num2DenseSublists n := by
    sorry

/-- Number of odd divisors of n (A001227). -/
def A001227 (n : ℕ) : ℕ := (n.divisors.filter Odd).card

/-- Number of odd divisors m of n such that there is a divisor d of n with d < m < 2*d (A239657). -/
def A239657 (n : ℕ) : ℕ :=
  (n.divisors.filter fun m => Odd m ∧ ∃ d ∈ n.divisors, d < m ∧ m < 2 * d).card

/--
Conjecture 1 / Theorem: "a(n) is the number of odd divisors of n except the 'e' odd
divisors described in A005279." - _Omar E. Pol_, Dec 21 2024.
"The conjecture 1 is true. For a proof see A379288." - _Hartmut F. W. Hoft_, Jan 21 2025.
Equivalently, $a(n) = \text{A001227}(n) - \text{A239657}(n)$. - _Omar E. Pol_, Mar 23 2014
-/
@[category research solved, AMS 11]
theorem conjecture_1 (n : ℕ) (hn : 0 < n) :
    a n = A001227 n - A239657 n := by
  sorry

/--
Theorem: "a(p^k) = k + 1, where p is an odd prime and k >= 0."
- _Hartmut F. W. Hoft_, Dec 26 2016
-/
@[category research solved, AMS 11]
theorem a_odd_prime_pow (p k : ℕ) (hp : p.Prime) (ho : Odd p) :
    a (p ^ k) = k + 1 := by
  sorry

/--
Conjecture 3: "a(n) is the number of divisors p of n such that p is greater than
twice the adjacent previous divisor of n. The divisors p give the n-th row of A379288."
- _Omar E. Pol_, Aug 02 2025

Note: this is equivalent to `a_eq_num2DenseSublists` (Conjecture 2), since the divisors that
start a new 2-dense sublist are exactly those greater than twice their predecessor (plus the
smallest divisor).
-/
@[category research solved, AMS 11]
theorem conjecture_3 (n : ℕ) :
    a n = 1 + ((sortedDivisorsList n).zip (sortedDivisorsList n).tail).countP
      fun pair => pair.snd > 2 * pair.fst :=
  conjecture_2 n

/--
Conjecture 4: "a(A000290(n)) is odd." - _Omar E. Pol_, Oct 21 2025

That is, the number of parts in the symmetric representation of $\sigma(n^2)$ is always odd.
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/oeis-a237271-square-hexagonal-parity/blob/430c09114d4ad3a3a2654b9816c8bfdc3cdf38de/lean/OeisA237271ParityFC.lean#L19-L24"]
theorem conjecture_4 (n : ℕ) (hn : 0 < n) : Odd (a (n ^ 2)) := by
  sorry

/--
Conjecture 5: "a(A000384(n)) is odd." - _Omar E. Pol_, Oct 21 2025

That is, the number of parts in the symmetric representation of $\sigma(n(2n-1))$ is always odd,
where $n(2n-1)$ is the $n$-th hexagonal number.
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/KitaKen1/oeis-a237271-square-hexagonal-parity/blob/430c09114d4ad3a3a2654b9816c8bfdc3cdf38de/lean/OeisA237271ParityFC.lean#L26-L32"]
theorem conjecture_5 (n : ℕ) (hn : 0 < n) : Odd (a (n * (2 * n - 1))) := by
  sorry

lemma zip_tail_mem_of_consec (l : List ℕ) (hl : l.Pairwise (· < ·)) {a b : ℕ} (ha : a ∈ l)
    (hb : b ∈ l) (hab : a < b) (hno : ∀ c ∈ l, ¬ (a < c ∧ c < b)) :
    (a, b) ∈ List.zip l l.tail := by
  induction l with
  | nil => simp at ha
  | cons x t ih =>
    rw [List.pairwise_cons] at hl
    cases t with
    | nil =>
      simp at ha hb; omega
    | cons y t' =>
      simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons, Prod.mk.injEq]
      rcases List.mem_cons.mp ha with rfl | ha'
      · have hb' : b ∈ y :: t' := by
          rcases List.mem_cons.mp hb with h | h
          · omega
          · exact h
        rcases List.mem_cons.mp hb' with rfl | hb''
        · left; exact ⟨rfl, rfl⟩
        · exfalso
          have hy : y < b := (List.pairwise_cons.mp hl.2).1 b hb''
          exact hno y (by simp) ⟨hl.1 y (by simp), hy⟩
      · right
        have hxa : x < a := hl.1 a ha'
        have hb' : b ∈ y :: t' := by
          rcases List.mem_cons.mp hb with h | h
          · omega
          · exact h
        exact ih hl.2 ha' hb' (fun c hc => hno c (List.mem_cons_of_mem _ hc))

lemma carmichael_facts {k : ℕ} (hk : IsCarmichael k) : 2 < k ∧ ¬ k.Prime ∧ Odd k := by
  have h1 := hk 1 le_rfl (Nat.coprime_one_right k)
  obtain ⟨-, hnp, hk1⟩ := h1
  have hk2 : 2 < k := by
    by_contra h
    have : k = 2 := by omega
    exact hnp (this ▸ Nat.prime_two)
  refine ⟨hk2, hnp, ?_⟩
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  have hcop : k.Coprime (k - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [add_comm, Nat.coprime_add_self_left]; exact Nat.coprime_one_left m
  obtain ⟨hpp, -, -⟩ := hk (k - 1) (by omega) hcop
  have hpow : 1 ≤ (k - 1) ^ (k - 1) := Nat.one_le_pow _ _ (by omega)
  have hz : (((k - 1) ^ (k - 1) - 1 : ℕ) : ZMod k) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hpp
  rw [Nat.cast_sub hpow, Nat.cast_pow, Nat.cast_sub (by omega), ZMod.natCast_self] at hz
  have hodd : Odd (k - 1) := by
    obtain ⟨r, hr⟩ := hev; exact ⟨r - 1, by omega⟩
  rw [zero_sub, Nat.cast_one, hodd.neg_one_pow] at hz
  have h2 : ((2 : ℕ) : ZMod k) = 0 := by
    have : (-1 : ZMod k) - 1 = -((2 : ℕ) : ZMod k) := by push_cast; ring
    rw [this, neg_eq_zero] at hz; exact hz
  rw [ZMod.natCast_eq_zero_iff] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  omega

/--
Observation: "a(A002997(n)) >= 3, at least for 1 <= n <= 10000."
- _Omar E. Pol_, Oct 21 2025

That is, $a(k) \ge 3$ for every Carmichael number $k$.
A002997 is the sequence of Carmichael numbers: the composite numbers $k$ such that
$b^{k-1} \equiv 1 \pmod k$ for every $b$ coprime to $k$. This is `IsCarmichael`,
which also forces $k$ to be composite.

The observation holds for every odd composite $k$, so in particular for every Carmichael
number. Write $p$ for the least prime factor of $k$ and $q = k/p$. The two smallest divisors
of $k$ are $1$ and $p$, and the two largest are $q$ and $k$, so $(1, p)$ and $(q, k)$ are both
consecutive pairs in the sorted divisor list, and they are distinct because $1 < q$. Both
qualify: $p$ and $k$ are odd, $p \ge 2 \cdot 1$, and $k = pq \ge 3q > 2q$. Hence the count is
at least $2$ and $a(k) \ge 3$. A Carmichael number is odd: it is composite by the $b = 1$ case
of `IsCarmichael`, so $k > 2$, and if $k$ were even then the coprime base $k - 1 \equiv -1$
would give $k \mid (-1)^{k-1} - 1 = -2$.
-/
@[category research solved, AMS 11]
theorem observation_carmichael (k : ℕ) (hk : IsCarmichael k) :
    3 ≤ a k := by
  obtain ⟨hk2, hnp, hodd⟩ := carmichael_facts hk
  have hk0 : k ≠ 0 := by omega
  set p := k.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpd : p ∣ k := Nat.minFac_dvd k
  have hpk : p < k := (Nat.not_prime_iff_minFac_lt (by omega)).mp hnp
  have hp2 : 2 ≤ p := hp.two_le
  have hpodd : Odd p := by
    rcases hp.eq_two_or_odd' with h | h
    · exfalso; rw [h] at hpd; exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpd)
    · exact h
  set q := k / p with hqdef
  have hkq : k = p * q := (Nat.mul_div_cancel' hpd).symm
  have hq1 : 1 < q := by
    by_contra h
    interval_cases q <;> simp at hkq <;> omega
  unfold a
  simp only []
  set L := k.divisors.sort (· ≤ ·) with hLdef
  have hL : L.Pairwise (· < ·) := (Finset.sortedLT_sort _).pairwise
  have memL : ∀ d, d ∈ L ↔ d ∣ k := by
    intro d; simp [hLdef, Finset.mem_sort, Nat.mem_divisors, hk0]
  have pair1 : ((1 : ℕ), p) ∈ List.zip L L.tail := by
    refine zip_tail_mem_of_consec L hL ((memL 1).mpr (one_dvd k)) ((memL p).mpr hpd) (by omega) ?_
    rintro c hc ⟨h1, h2⟩
    have := Nat.minFac_le_of_dvd (by omega) ((memL c).mp hc)
    omega
  have pair2 : (q, k) ∈ List.zip L L.tail := by
    have hqd : q ∣ k := ⟨p, by rw [hkq]; ring⟩
    refine zip_tail_mem_of_consec L hL ((memL q).mpr hqd) ((memL k).mpr dvd_rfl) (by nlinarith) ?_
    rintro c hc ⟨h1, h2⟩
    obtain ⟨d, hd⟩ := (memL c).mp hc
    have hd2 : 2 ≤ d := by
      rcases Nat.lt_or_ge d 2 with h | h
      · interval_cases d <;> simp at hd <;> omega
      · exact h
    have hpd' : p ≤ d := Nat.minFac_le_of_dvd hd2 ⟨c, by rw [hd]; ring⟩
    nlinarith
  have hne : ((1 : ℕ), p) ≠ (q, k) := by
    intro h; simp only [Prod.mk.injEq] at h; omega
  set P : ℕ × ℕ → Bool := fun pair => decide (Odd pair.2 ∧ pair.2 ≥ 2 * pair.1) with hP
  have hcount : 2 ≤ (List.zip L L.tail).countP P := by
    rw [List.countP_eq_length_filter]
    have hsub : ({((1 : ℕ), p), (q, k)} : Finset (ℕ × ℕ)) ⊆ ((List.zip L L.tail).filter P).toFinset := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [List.mem_toFinset, List.mem_filter]
      rcases hx with rfl | rfl
      · exact ⟨pair1, by simp [hP, hpodd]; omega⟩
      · exact ⟨pair2, by simp [hP, hodd]; nlinarith⟩
    have := (Finset.card_le_card hsub).trans (List.toFinset_card_le _)
    rwa [Finset.card_pair hne] at this
  show 3 ≤ 1 + (List.zip L L.tail).countP P
  omega

end OeisA237271
