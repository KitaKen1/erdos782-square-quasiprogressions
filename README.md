# Erdős 782(i) — Quasi-progressions of squares have bounded length

[Erdős Problem #782](https://www.erdosproblems.com/782) asks two questions about the squares. Formal Conjectures (FC) records part (i) as a research question. [FC statement](https://github.com/google-deepmind/formal-conjectures/blob/2de491f90132d3f3fac934edf5bd72acb3dfd15c/FormalConjectures/ErdosProblems/782.lean#L77-L89)

> [!NOTE]
> **Problem (i).** Is there a fixed integer $C>0$ such that for every length $k$ there are squares $x_0<\cdots<x_{k-1}$ whose successive differences all lie in $[d,d+C]$ for some integer $d\ge1$? The value of $d$ may vary with the sequence.

This repository proves in Lean that the answer to part (i) is **no**. [Lean theorem](lean/Comparator/Candidate.lean#L11)

### Exact Formal Conjectures target

The proposition under `¬` is the type of FC's `erdos_782.parts.i`. The generator copies that type and the original `ContainsQuasiProgression` definition from the pinned FC source. The proof formalizes the needed case of Gerver–Ramsey and applies AxiomMath’s formalization of Faltings’s theorem. [Pinned FC source](verification/reference/782.lean#L77-L89) · [Generated Lean module](lean/Comparator/FCStatement.lean)

```lean
theorem erdos_782.parts.i_neg :
    ¬ (∃ C : ℕ, 0 < C ∧ ∀ k : ℕ,
      ContainsQuasiProgression {n : ℕ | IsSquare n} C k) :=
  Erdos782Reduction.not_exists_width Erdos782Walk.planarWalk Erdos782Arithmetic.sixRootFiniteness
```

### Mathematical Explanation (AI generated)

**1. Extract six collinear points from the final block.** Fix $C$ and take $N=N(C)$ from Gerver and Ramsey's theorem for six collinear points, with step set $\{(1,j):0\le j\le C\}$. Consider a sequence of length $k\ge N+1$ and let $m=k-1-N$. For $0\le i\le N$, put $e_i=x_{m+i}-(m+i)d$. The points $(i,e_i)$ form a lattice walk with the required steps. Six points lie on one line, at indices $b+h_1,\ldots,b+h_6$ with $0=h_1<h_2<\cdots<h_6\le N$. The slope $a$ of that line lies in $[0,C]$ because each increment of $e_i$ lies in that interval. Set $q=d+a$ and $X=x_{m+b}$. Then $q$ is positive and rational, and $x_{m+b+h_j}=X+qh_j$ for every $j$. [Gerver–Ramsey, Theorem 1](https://msp.org/pjm/1979/83-2/pjm-v83-n2-p08-s.pdf)

**2. Bound the normalized position by rational-point finiteness.** Write $r_j^2=X+qh_j$ with $r_j$ an integer. Put $t=X/q$ and $y=(\prod_{j=1}^6r_j)/q^3$. Multiplying the six equations gives

```math
y^2=\prod_{j=1}^6(t+h_j).
```

The smooth projective model is a double cover of the projective line branched at the six distinct points $-h_j$, with no ramification at infinity because the degree is even. Riemann–Hurwitz gives genus two. By Faltings's theorem, each such curve has only finitely many rational points. Since the six offsets come from $\{0,\ldots,N\}$, only finitely many curves occur. Choose a nonnegative integer $T=T(N)$ bounding the affine rational $t$-coordinates of all of them from above. The Lean proof uses Tau Ceti’s hyperelliptic genus formula and identifies its genus with the adelic genus in AxiomMath’s formulation. For a rational abscissa $t$ with a nonzero ordinate, the corresponding degree-one place restricts to the place of $X-t$, so distinct such abscissae give distinct places. An abscissa with ordinate zero is a root of the sextic. [Faltings (1983)](https://doi.org/10.1007/BF01388432) · [Lean application](lean/SexticFiniteness.lean) · [AxiomMath’s Faltings theorem](https://github.com/AxiomMath/Mordell/blob/82a30cb7857f6e3cfdb1be91f5533c0ccb57d493/Mordell/MordellConjecture/FunctionField.lean#L46)

**3. Bound the length.** The positive gaps give $x_i\ge id$, so $X\ge md$. The rational-point bound gives $X\le qT\le(d+C)T\le d(C+1)T$, since $d\ge1$. Dividing by $d$ yields $m\le(C+1)T$. Therefore

```math
k\le L(C):=N(C)+1+(C+1)T(N(C)).
```

The bound also holds for $k\le N$. It depends only on $C$, which proves the conjecture of Brown, Freedman, and Shiue. [*Progressions of squares*, §3](https://ajc.maths.uq.edu.au/pdf/27/ajc_v27_p187.pdf#page=4)

## Appendix: Timeline

| Year | Result |
| --- | --- |
| 1979 | Gerver and Ramsey proved that sufficiently long planar lattice walks with bounded steps contain any prescribed number of collinear points. [Theorem 1](https://msp.org/pjm/1979/83-2/pjm-v83-n2-p08-s.pdf) |
| 1983 | Faltings proved finiteness of rational points on smooth projective curves of genus at least two over number fields. [Paper](https://doi.org/10.1007/BF01388432) |
| 1990 | Brown, Erdős, and Freedman asked whether the squares have arbitrarily long quasi-progressions of some fixed diameter. [§5](https://www.sfu.ca/~vjungic/tbrown/tom-35.pdf) |
| 2003 | Brown, Freedman, and Shiue conjectured a length bound for every fixed diameter. [§3, p. 190](https://ajc.maths.uq.edu.au/pdf/27/ajc_v27_p187.pdf#page=4) |
| 2026 | The proof above combines the two theorems using the last block of a quasi-progression. [Lean reduction](lean/Erdos782QuasiProgressions.lean) |

## Appendix: Verification by Lean Comparator on GitHub CI runner

The [parallel Lean comparator workflow](.github/workflows/comparator-parallel.yml) runs on pushes to this branch. The [single-runner workflow](.github/workflows/comparator.yml) is available from the Actions tab. It checks the pinned FC snapshot and builds the reference statement in a project with the pinned Mathlib dependency. The workflows use the pinned public Stacks and Mordell cache. The parallel workflow builds the remaining dependencies in topological order across its jobs. The final job builds the candidate, exports the proof with Lean, and compares it against the reference. Comparator permits only `propext`, `Classical.choice`, and `Quot.sound`. It checks the exported proof with nanoda and Lean’s kernel. A fresh Lean kernel also replays the export. [Source check](verification/prepare_sources.py) · [Comparator configuration](lean/comparator.json)

The proof and workflow under verification are at commit `2b11bcc`. [GitHub Actions run](https://github.com/KitaKen1/erdos782-square-quasiprogressions/actions/runs/44353268582)

### Certification within 90 days

Each workflow attempt uploads an artifact named `comparator-<run-id>-<attempt>` with 90-day retention. A successful attempt contains the checked Lean signature in `statement.log`, both kernel verdicts in `fc-target.log`, the result in `result.json`, and the fresh replay log and status.

### Certification after 90 days

Before an artifact expires, [archive-run.py](verification/archive-run.py) can preserve a successful attempt with an authenticated GitHub CLI. It verifies the tested commit and GitHub's artifact digest and saves the original ZIPs, run metadata, verification logs, and `SHA256SUMS`.

```sh
python3 verification/archive-run.py --repo OWNER/REPO --run RUN_ID \
  --attempt ATTEMPT --expected-commit FULL_SHA --output verification/logs/ci-RUN_ID
```

### Reproduce the verification

With elan and bubblewrap installed on Linux, run from the repository root. The first source build compiles the pinned Stacks and Mordell dependencies. [Pinned Lean project](lean/)

```sh
python3 verification/prepare_sources.py --check
(cd lean && lake exe cache get)
python3 verification/verify.py
bash verification/export-solution.sh /tmp/erdos782-proof.ndjson.gz
```

For a trusted macOS checkout, pass `--trusted-local` to `verification/verify.py`. To check a previously generated proof export, decompress the archive and pass its NDJSON path with `--solution-export`.

## AI usage disclosure

This formalization, mathematical exploration, proof development, and documentation were produced by Kenta Kitamura with assistance from OpenAI Codex using GPT-6.2 Astra.
