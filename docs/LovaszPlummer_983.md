# A Lean 4 proof of the Lovász–Plummer bound with constant 1/983

Every bridgeless cubic graph on `n` vertices has at least `2^(n/983)` perfect matchings.
The Lean 4 proof is the file [`Proofs/T_LovaszPlummerConjecture_lovasz_plummer_conjecture_variants_explicit.lean`](../Proofs/T_LovaszPlummerConjecture_lovasz_plummer_conjecture_variants_explicit.lean) of this repository; this
document describes it. The proof follows Esperet, Kardoš, King, Král' and Norine,
*Exponentially many perfect matchings in cubic graphs*, Adv. Math. 227 (2011), 1646–1664
(arXiv:1012.2878), with the changes listed in the description of the pull request
[google-deepmind/formal-conjectures #6854](https://github.com/google-deepmind/formal-conjectures/pull/6854).

Status: published. The file was checked by the Lean kernel and by `leanprover/comparator` on
2026-10-06 (`JUDGE: PASS`) and is in this repository (anatoliiohorodnyk/lean-fc-proofs) since
commit `e1059f02264088e9fc4e2866855b8cf68d9cbeda`. The pull request above links it from the statement in formal-conjectures.

## The two theorems

The file is a copy of `FormalConjectures/Wikipedia/LovaszPlummerConjecture.lean` from
google-deepmind/formal-conjectures. Its target is the statement of that repository, unchanged:

```lean
@[category research solved, AMS 5]
theorem lovasz_plummer_conjecture.variants.explicit
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless) :
    (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G
```

It is derived, by monotonicity of `2^x`, from a stronger statement that uses Mathlib notions
only (no definition of the formal-conjectures file):

```lean
theorem lovasz_plummer_explicit_internal
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcubic : ∀ v, G.degree v = 3) (hbridgeless : ∀ e ∈ G.edgeSet, ¬G.IsBridge e) :
    (2 : ℝ) ^ ((Fintype.card V : ℝ) / 983) ≤
      ({M : G.Subgraph | M.IsPerfectMatching}.ncard : ℕ)
```

Both are in the namespace `LovaszPlummerConjecture` (lines 34242 and 34280 of the file).
The other three statements of the original file (`lovasz_plummer_conjecture`,
`sheehan_conjecture`, `sheehan_conjecture.variants.thomassen`) are left as they are, with
`sorry`; they are not used.

## Versions

| | |
|---|---|
| Lean | `leanprover/lean4:v4.33.1` |
| formal-conjectures | commit `df3f12d7bd06feb3f71ae37abae0ca7cb798d9b1` |
| Mathlib (pinned by that commit) | `0df444a360eaa60ab8c11dca51a86af692955474` (`v4.33.1`) |
| comparator | `leanprover/comparator` at `fd5d5bcf14177b187f66d4502071268d877887c3` |

The theorem file of formal-conjectures at the pinned commit is byte-identical to the one on
`main` on 2026-10-06 (`main` = `89294ea0…`): upstream has not changed the statement.

## Building

This repository is a Lake project (`lakefile.toml`) that requires formal-conjectures at the
commit above; `lean-toolchain` and `lake-manifest.json` pin the versions of the table. The
library `Proofs` contains every file of `Proofs/`, and it is the default target, so name the
module to build this file only:

    lake exe cache get          # Mathlib build products
    lake build Proofs.T_LovaszPlummerConjecture_lovasz_plummer_conjecture_variants_explicit

(A plain `lake build` builds all proofs of the repository.) The library is configured with
`warn.sorry = false`, so the three statements left as `sorry` produce no warning.

Measured on the build host (one `lean` process; the file is elaborated sequentially):

| run | wall time | peak memory |
|---|---|---|
| `lake build` of the file (level-1 check) | 25 min 31 s | 8.6 GB |
| comparator in a fresh sandbox copy (build + export + kernel replay) | 49 min 13 s | not reported by the tool; limit 32 GB |

About 22 of the 26 minutes are the kernel evaluation of the certificate checks.

## Axioms

    'LovaszPlummerConjecture.lovasz_plummer_conjecture.variants.explicit' depends on axioms:
    [propext, Classical.choice, Quot.sound]

(from the log of the check). `lovasz_plummer_explicit_internal` is used by the target,
so its axioms are among these three. There is no `sorryAx`, no `native_decide`, no
`Lean.ofReduceBool`: every `decide` in the file is `decide +kernel`, evaluated by the kernel.
The comparator additionally checks that the statement and all definitions it depends on are
those of the formal-conjectures file.

## Map of the file (34 326 lines)

Multigraphs are given by an edge type `E`, end maps `α β : E → W` and a vertex set
`L : Finset W`. Line numbers are those of `Proofs/T_LovaszPlummerConjecture_lovasz_plummer_conjecture_variants_explicit.lean`.

| lines | content | main declarations |
|---|---|---|
| 1–38 | header of the original file | |
| 39–1 970 | cuts, perfect matchings; Edmonds' perfect matching polytope theorem; Petersen in the form "every edge of a cubic bridgeless multigraph is in a perfect matching"; reduction of the simple-graph statement to connected multigraphs; the numeric inequality `2^(83/200) ≤ 4/3` | `ep_edmonds` (1424), `ep_cubic_edge_in_pm` (1508), `lp_of_multigraph` (1774), `lp_reduce_connected` (1927), `lp_const9` (1966) |
| 1 970–9 100 | burls and foliages (Section 2 of the paper), Kotzig's theorem, cut-contractions, a 4-cut with two matchings is a burl, small-cut decompositions and hubs | `ep_kotzig` (2657), `ep_cut4_burl` (6543), `ep_max_decomp_cyc4` (8453) |
| 9 100–11 920 | relevant triangles and the family replacing "elementary twigs"; nested 2-cuts; the ladder lemmas of the earlier 1/4749 proof (still present, no longer used by the target) | `ep_relevant_meets` (9105), `ep_nested2_burl` (9814) |
| 11 920–14 440 | the certificate checker for burls and its soundness; chain patterns and their model graphs; the coverage search and its soundness; a chain of ten nodes carries a burl | `cCheck_sound` (12202), `LpCert.sound` (12314), `lpCov_sound` (12485), `ep_burl_iso` (12516), `ep_chain_burl10` (14396) |
| 14 449–24 216 | data: the 1393 chain certificates with their two checks each, the search tree over them, and the coverage statement | `lpC1 … lpC1900`, `lpTree` (24201), `lpTree_cov` (24213) |
| 24 217–24 740 | foliage weights, twigs are burls, leaves of the decomposition | `epFw` (24381), `ep_twig_burl` (24576) |
| 24 739–25 160 | sizes of leaves, atoms and chains by the size of the cut; a second burl in a chain with a 2-cut at an end; three more coverage statements | `ep_chain_size_cut` (24858), `ep_chain_burl_top2` (25072), `lpTree_covF1a/F1b/F2` (25147–25153) |
| 25 159–25 600 | graphs without a core (Lemma 11, Corollary 12) | `ep_lemma11` (25209), `ep_cor12` (25590) |
| 25 600–27 400 | splitting along a path (Lemmas 23/24); pruning with a budget; local structure of a cyclically 4-edge-connected graph | `epSp_cut_ge_two` (25998), `ep_prune_budget` (26755), `ep_cyc4_local` (27259) |
| 27 406–31 434 | the splitting lever: sets with a 5-cut, 18 certificates, bad splits and the good choice, the foliage lift with loss `2β₁ − β₂` | `ep_cut4_burl_cyc4` (27887), `ep_cut5_reduce` (28438), `ep_burl_of_model` (28836), `ep_cut5_burl` (29623), `ep_good_choice` (30802), `ep_cyc4_local_good` (31202), `epSp_fol_good` (31254) |
| 31 435–33 296 | graphs with a core (Lemma 13/14): one split, Case 1 by four splits, core partitions, Case 2 | `ep_split_package` (31435), `ep_l13_cyc4` (31562), `ep_l13_case2a` (32445), `ep_cyc4_fol_avoid` (32908), `ep_l13_case2b` (33059), `ep_lemma13` (33218) |
| 33 296–34 241 | pruning with the dichotomy (factor 2.5), counting from a foliage, the bound for connected multigraphs | `ep_prune_dich` (34113), `ep_fol0_count` (34136), `lp_multigraph_bound` (34162) |
| 34 242–34 326 | the corollary, the original statements, the target | `lovasz_plummer_explicit_internal`, `lovasz_plummer_conjecture.variants.explicit` |

Constants: `α = 83/18400`, `β₂ = 28α`, `β₁ = 57α`, `γ = 118α`;
`1/983 ≥ 1/(2.5·(3·57 + 18400/83) + 1)`.

## What is checked by computation, and how

All of it is evaluated inside the Lean kernel (`decide +kernel`); no external solver result is
trusted.

1. **1393 chain certificates** (`lpC…`, type `LpCertP`). Each certifies that one pattern of at
   most ten consecutive nodes of a chain is a burl: it lists integer dual multipliers of a
   small linear program and, for the local matchings that need one, an alternating flip set.
   `LpCertP.check` enumerates the local matchings of the pattern's graph and verifies the dual
   inequality for each with integer arithmetic; `cCheck_sound`/`LpCert.sound` prove that an
   accepted certificate implies the burl property. A second check per certificate (`…_tok`)
   verifies the layout data used to transfer the pattern to a real chain. 2786 checks.
2. **Coverage of all chains.** `lpTree_cov : lpCov lpTree 10 [] = true` is an exhaustive search
   showing that every admissible pattern of ten nodes contains a certified pattern;
   `lpCov_sound` turns it into a statement about chains. Three further searches
   (`lpTree_covF1a`, `lpTree_covF1b`, `lpTree_covF2`) do the same for chains of seven nodes with
   a cut of size two at one end.
3. **18 lever certificates** (`lvC_…`, type `LpCert`), for the graphs that occur in the
   classification of sets with a 5-cut and in the merge of two such sets. Same checker.
   For each, `LpCert.ModelOK` (also `decide +kernel`) verifies the combinatorial side
   conditions under which a certificate graph can be identified with a vertex set of the
   real multigraph (`ep_burl_of_model`).
4. A handful of small decidable facts about the four model graphs (`lvKey…`, `lvPerm…`,
   `lvGlue…`).

The certificate checks are stated as `def name : c.check = true := by decide +kernel` rather
than `theorem`: Lean elaborates theorems asynchronously, and with 2786 of them in one file
the build ran out of memory (16 GB); as definitions they are elaborated one after the other
and the peak stays at 8–9 GB. The proposition and its kernel check are the same.

The certificates were found by a linear-programming solver and the coverage by a Python
search; those programs are not part of the proof.

## Provenance

The file is generated, not written by hand. A script (`lp_assemble.py`, variant `E1p`) takes
the helper text of the 1/4749 proof, substitutes the constants, patches a fixed list of declarations, and
inserts the new modules and the certificate data. **The generator, its inputs and the logs of
the check and of the comparator are not in this repository**; they are in the author's working
repositories. Two of the inputs are pinned by hash and asserted by the script:

| | sha256 |
|---|---|
| input: sizes by cut, second burl | `0769b7f52ab03eb57fbab64ca9b65edc20fad4fab769fce971cff82eb016f66e` |
| input: the splitting lever | `15c4ab67b7ceb3093d5bd80379e8a3c058d448a4f0247bfbda7e022774bbbd8d` |
| result: `Proofs/T_LovaszPlummerConjecture_lovasz_plummer_conjecture_variants_explicit.lean` | `9fac21f493a4a226769a13443245a4c6ccf9064e8e3ef483fa5a602cb14f4a7e` |

Earlier states that passed the same check and comparator run (the names are tags of the
author's working repositories, not of this one):

| state | internal constant | what was new |
|---|---|---|
| published 2026-10-04, `Proofs/T_LovaszPlummerConjecture_lovasz_plummer_conjecture.lean` | 1/4749 | the existence statement `lovasz_plummer_conjecture` |
| `explicit-1308` | 1/1308 | certified chains of ten nodes, pruning factor 2.5, exact vertex count in Lemma 14 |
| `explicit-1289` | 1/1289 | exact branching step in Lemma 11 |
| `explicit-1152` | 1/1152 | sizes by cut, root case of Lemma 11 |
| `explicit-983` | 1/983 | the splitting lever |
| `explicit-983-pub` | 1/983 | this file: the `explicit-983` text with comments and docstrings cleaned (25 comment lines; no statement or proof line differs); checked and judged again |

Files in this repository that belong to this proof: `Proofs/T_LovaszPlummerConjecture_lovasz_plummer_conjecture_variants_explicit.lean` and this document
(`docs/LovaszPlummer_983.md`).
