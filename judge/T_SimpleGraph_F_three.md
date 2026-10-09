# Comparator and axiom record: `SimpleGraph.F_three`

Task id `T_SimpleGraph_F_three`. Two runs of the same pipeline on the same proof file: the original
judge run of 2026-10-06 and a repeat on 2026-10-09 made for this record. Both passed.

## What was checked

| item | value |
|---|---|
| theorem | `SimpleGraph.F_three : F 3 = 7` |
| statement source | `FormalConjectures/Paper/DegreeSequencesTriangleFree.lean` of google-deepmind/formal-conjectures at `df3f12d7bd06feb3f71ae37abae0ca7cb798d9b1` |
| proof file | `Proofs/T_SimpleGraph_F_three.lean` (theorem at line 569) |
| proof commit | `fc4f1f1d43b54106b0f932518075fef57829d6fb` of this repository |
| proof file sha256 | `77624d3f4d6f982709ca6649ee74582bf86e2b04350dc8921d940666886c1b22` |
| Lean toolchain | `leanprover/lean4:v4.33.1` |
| Mathlib | `0df444a360eaa60ab8c11dca51a86af692955474` (see note 1) |
| Comparator | leanprover/comparator at `fd5d5bcf14177b187f66d4502071268d877887c3` (see note 2) |
| lean4export | leanprover/lean4export, tag `v4.33.1`, built with the toolchain above (see note 2) |
| landrun | zouuup/landrun at `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` (see note 2) |

The sha256 was verified three ways before the repeat run: `git show fc4f1f1:Proofs/T_SimpleGraph_F_three.lean`,
the file submitted to the judge, and the snapshot kept by the original run all have this hash.

Comparator configuration, as written by the pipeline (`comparator.json`):

```json
{"challenge_module":"Challenges.T_SimpleGraph_F_three","solution_module":"Proofs.T_SimpleGraph_F_three","theorem_names":["SimpleGraph.F_three"],"permitted_axioms":["propext","Quot.sound","Classical.choice"]}
```

`Challenges/T_SimpleGraph_F_three.lean` is an unmodified copy of the statement source file from the
formal-conjectures checkout. Comparator is run as `lake env comparator comparator.json` in a
fresh copy of a workspace in which the proof file was never compiled before.

The same file still contains the other target of the paper, `SimpleGraph.F_four_le`, with `sorry`.
It is not part of this check; see `T_SimpleGraph_F_four_le.md`.

## Results

| | original run | repeat run |
|---|---|---|
| finished (UTC) | 2026-10-06T17:21:59+00:00 | 2026-10-09T09:02:08+00:00 |
| host | `b01` (private compute host) | `b01` |
| verdict | pass | pass |
| build of `Challenges.T_SimpleGraph_F_three` in the sandbox | 5.3 s | 21 s |
| build of `Proofs.T_SimpleGraph_F_three` in the sandbox | 123 s | 323 s |
| wall time of the whole judge command | not recorded | 787 s (see note 3) |
| peak memory | 17.3 GB for the build (see note 5) | not measured (see note 4) |

Comparator verdict, verbatim, the last two lines of the log in both runs:

```
Lean default kernel accepts the solution
Your solution is okay!
```

`#print axioms SimpleGraph.F_three`, from the repeat run (the pipeline joins wrapped lines into
one line; otherwise verbatim):

```
'SimpleGraph.F_three' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The original run made the same axiom check as a precondition of the judge step, but its output was
not kept.

## Logs

| file | content |
|---|---|
| `T_SimpleGraph_F_three.2026-10-06.comparator.log` | original run: complete Comparator output |
| `T_SimpleGraph_F_three.2026-10-06.meta.txt` | original run: declaration, FC revision, toolchain, timestamp |
| `T_SimpleGraph_F_three.2026-10-09.comparator.log` | repeat run: complete Comparator output |
| `T_SimpleGraph_F_three.2026-10-09.meta.txt` | repeat run: declaration, FC revision, toolchain, timestamp |
| `T_SimpleGraph_F_three.2026-10-09.fc-check.out` | repeat run: output of the level-1 check, with the `#print axioms` line |
| `T_SimpleGraph_F_three.2026-10-09.fc-judge.out` | repeat run: output of the judge command |

The two Comparator logs differ only in the two build times.

## Notes

1. The Mathlib revision is the one in `lake-manifest.json` of this repository at the proof commit,
   which is what formal-conjectures at the revision above resolves to. The manifest on the compute
   host was not read back for this record.
2. Tool revisions are the ones pinned in the setup script of the compute host. They were not read
   back from the installed binaries for this record.
3. Measured on the calling machine around the whole command. It includes the level-1 check
   (26 s, a cache replay), the copy of the workspace, both builds, the export and the kernel
   replay by Comparator. The host was not checked for other load, and the builds were slower than
   in the original run.
4. The Comparator step runs in a cgroup with `MemoryMax=32G` and finished, so it stayed under that
   limit; the pipeline does not record its peak. The level-1 check of the repeat run reported
   0.3 GB, but that build was a cache replay and says nothing about the proof.
5. 17.3 GB is the peak of the `lake build` cgroup in the level-1 check of 2026-10-06 (the script
   divides bytes by 2^30). The number was written down in the work notes at the time; the raw
   output of that check was not kept. Almost all of it is the kernel enumeration of the graphs on
   at most 6 vertices.

## Reproduce

Needs `comparator`, `lean4export` (built with Lean v4.33.1) and `landrun` on `PATH`, at the
revisions above. These commands mirror what the pipeline does on the compute host; they were not
run in this form from a clone of this repository.

```sh
git clone https://github.com/anatoliiohorodnyk/lean-fc-proofs && cd lean-fc-proofs
git checkout fc4f1f1d43b54106b0f932518075fef57829d6fb
sha256sum Proofs/T_SimpleGraph_F_three.lean   # 77624d3f4d6f982709ca6649ee74582bf86e2b04350dc8921d940666886c1b22
lake exe cache get
mkdir -p Challenges
cp .lake/packages/formal_conjectures/FormalConjectures/Paper/DegreeSequencesTriangleFree.lean \
   Challenges/T_SimpleGraph_F_three.lean
cat > comparator.json <<'EOF'
{"challenge_module":"Challenges.T_SimpleGraph_F_three","solution_module":"Proofs.T_SimpleGraph_F_three","theorem_names":["SimpleGraph.F_three"],"permitted_axioms":["propext","Quot.sound","Classical.choice"]}
EOF
lake env comparator comparator.json
```

Axioms:

```sh
printf 'import Proofs.T_SimpleGraph_F_three\n#print axioms SimpleGraph.F_three\n' > Ax.lean
lake env lean Ax.lean
```

AI-usage disclosure: Claude Opus 5.5 (Anthropic) was used as assistant.
