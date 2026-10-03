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

def Q237 (L : List ℕ) (m : ℕ) : Bool := decide (Odd m ∧ ¬ ∃ d ∈ L, d < m ∧ m < 2 * d)

def P237 (p : ℕ × ℕ) : Bool := decide (Odd p.2 ∧ p.2 ≥ 2 * p.1)

lemma a237_zip_append (x : ℕ) : ∀ (L : List ℕ) (hne : L ≠ []),
    zip (L ++ [x]) (L ++ [x]).tail = zip L L.tail ++ [(L.getLast hne, x)]
  | [], h => absurd rfl h
  | [a], _ => by simp
  | a :: b :: rest, _ => by
    have ih := a237_zip_append x (b :: rest) (by simp)
    simp only [List.cons_append, List.tail_cons, List.zip_cons_cons] at ih ⊢
    rw [ih]
    simp [List.getLast_cons]

lemma a237_le_last (L : List ℕ) (hs : L.Pairwise (· < ·)) (hne : L ≠ []) :
    ∀ d ∈ L, d ≤ L.getLast hne := by
  intro d hd
  have hL := List.dropLast_append_getLast hne
  rw [← hL] at hs hd
  rw [List.pairwise_append] at hs
  rcases List.mem_append.mp hd with h | h
  · exact (hs.2.2 d h _ (List.mem_singleton_self _)).le
  · rw [List.mem_singleton.mp h]

lemma a237_main (L : List ℕ) : L.Pairwise (· < ·) → (hne : L ≠ []) →
    (L.filter (Q237 L)).length =
      (if Odd (L.head hne) then 1 else 0) + (zip L L.tail).countP P237 := by
  induction L using List.reverseRecOn with
  | nil => intro _ h; exact absurd rfl h
  | append_singleton L x ih =>
    intro hs hne
    by_cases hL : L = []
    · subst hL
      by_cases hx : Odd x <;> simp [Q237, hx]
    · rw [List.pairwise_append] at hs
      obtain ⟨hsL, -, hlt⟩ := hs
      have hx : ∀ a ∈ L, a < x := fun a ha => hlt a ha x (List.mem_singleton_self _)
      have ih' := ih hsL hL
      rw [List.filter_append, List.length_append, a237_zip_append x L hL, List.countP_append,
        List.head_append_of_ne_nil hL]
      have hcongr : L.filter (Q237 (L ++ [x])) = L.filter (Q237 L) := by
        apply List.filter_congr
        intro m hm
        simp only [Q237, List.mem_append, List.mem_singleton]
        congr 1
        apply propext
        constructor
        · rintro ⟨ho, hno⟩; refine ⟨ho, fun ⟨d, hd, h1, h2⟩ => hno ⟨d, List.mem_append.mpr (Or.inl hd), h1, h2⟩⟩
        · rintro ⟨ho, hno⟩
          refine ⟨ho, fun ⟨d, hd, h1, h2⟩ => ?_⟩
          rcases List.mem_append.mp hd with hd | hd
          · exact hno ⟨d, hd, h1, h2⟩
          · rw [List.mem_singleton] at hd; subst hd; have := hx m hm; omega
      rw [hcongr, ih']
      have hlast := a237_le_last L hsL hL
      have hlastmem : L.getLast hL ∈ L := List.getLast_mem hL
      have hxlast := hx _ hlastmem
      have hQx : Q237 (L ++ [x]) x = P237 (L.getLast hL, x) := by
        simp only [Q237, P237, List.mem_append, List.mem_singleton]
        congr 1
        apply propext
        constructor
        · rintro ⟨ho, hno⟩
          refine ⟨ho, ?_⟩
          by_contra hc
          exact hno ⟨L.getLast hL, List.mem_append.mpr (Or.inl hlastmem), hxlast, by omega⟩
        · rintro ⟨ho, hge⟩
          refine ⟨ho, fun ⟨d, hd, h1, h2⟩ => ?_⟩
          rcases List.mem_append.mp hd with hd | hd
          · have := hlast d hd; omega
          · rw [List.mem_singleton] at hd; omega
      simp only [List.filter_cons, List.filter_nil, hQx, List.countP_cons, List.countP_nil]
      cases P237 (L.getLast hL, x) <;> simp <;> omega

lemma a237_len_filter (s : Finset ℕ) (p : ℕ → Prop) [DecidablePred p] :
    ((s.sort (· ≤ ·)).filter (fun m => decide (p m))).length = (s.filter p).card := by
  rw [Finset.card_def, Finset.filter_val, ← Finset.sort_eq s (· ≤ ·), Multiset.filter_coe,
    Multiset.coe_card]

/--
Conjecture 1 / Theorem: "a(n) is the number of odd divisors of n except the 'e' odd
divisors described in A005279." - _Omar E. Pol_, Dec 21 2024.
"The conjecture 1 is true. For a proof see A379288." - _Hartmut F. W. Hoft_, Jan 21 2025.
Equivalently, $a(n) = \text{A001227}(n) - \text{A239657}(n)$. - _Omar E. Pol_, Mar 23 2014
-/
@[category research solved, AMS 11]
theorem conjecture_1 (n : ℕ) (hn : 0 < n) :
    a n = A001227 n - A239657 n := by
  set L := n.divisors.sort (· ≤ ·) with hL
  have hpw : L.Pairwise (· < ·) := (Finset.sortedLT_sort _).pairwise
  have hmem : ∀ m, m ∈ L ↔ m ∈ n.divisors := fun m => Finset.mem_sort _
  have h1 : 1 ∈ L := (hmem 1).mpr (Nat.mem_divisors.mpr ⟨one_dvd _, by omega⟩)
  have hne : L ≠ [] := List.ne_nil_of_mem h1
  have hmain := a237_main L hpw hne
  have hhead : L.head hne = 1 := by
    have hh : L.head hne ∈ L := List.head_mem hne
    have hpos : 1 ≤ L.head hne := Nat.pos_of_mem_divisors ((hmem _).mp hh)
    have hle : L.head hne ≤ 1 := by
      rcases L with _ | ⟨b, t⟩
      · exact absurd rfl hne
      · simp only [List.head_cons]
        rcases List.mem_cons.mp h1 with h | h
        · omega
        · exact ((List.pairwise_cons.mp hpw).1 1 h).le
    omega
  rw [hhead] at hmain
  simp only [odd_one, if_true] at hmain
  have ha : a n = 1 + (zip L L.tail).countP P237 := rfl
  rw [ha, ← hmain]
  have hfilt : L.filter (Q237 L) =
      L.filter (fun m => decide (Odd m ∧ ¬ ∃ d ∈ n.divisors, d < m ∧ m < 2 * d)) := by
    apply List.filter_congr
    intro m _
    simp only [Q237, hmem]
  rw [hfilt, a237_len_filter]
  unfold A001227 A239657
  have := Finset.card_filter_add_card_filter_not (s := n.divisors.filter Odd)
    (p := fun m => ∃ d ∈ n.divisors, d < m ∧ m < 2 * d)
  rw [Finset.filter_filter, Finset.filter_filter] at this
  omega

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
  sorry

end OeisA237271
