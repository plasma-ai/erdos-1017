# Erdős Problem 1017: clique partitions of graphs of given size

This Lean 4 project concerns [Erdős Problem 1017](https://www.erdosproblems.com/1017), as cataloged by Thomas F. Bloom. Let `f(n, k)` be the least number such that the edges of every graph with `n` vertices and `k` edges can be partitioned into at most `f(n, k)` cliques, a single edge counting as a clique. Erdős, Goodman and Pósa proved `f(n, k) ≤ ⌊n²/4⌋`, which the complete balanced bipartite graph attains. Erdős asked whether this bound can be sharpened when `k > n²/4`, and Bloom's catalog asks for an estimate of `f(n, k)` there. We determine `f(n, k)` to within `o(n²)` at every edge density: `f(n, k) = n² B(k/n²) + o(n²)` uniformly in `k`, for an explicit continuous piecewise-algebraic function `B` on `[0, 1/2]`:

```
for every η > 0 there is N such that, for all n ≥ N and all 0 ≤ k ≤ n(n − 1)/2,
    |f(n, k)/n² − B(k/n²)| < η.
```

This provides an asymptotic resolution of Erdős Problem 1017, as posed by Erdős and as stated by Bloom: for `k > n²/4` it replaces `⌊n²/4⌋` by `n² B(k/n²) + o(n²)`, and the lower bound shows that this leading term is exact.

`Challenge.lean` states this theorem with only Mathlib imports, copying the definitions of `f` and of clique edge partitions verbatim from `formal-conjectures`, and `Solution.lean` proves it.

Plasma AI found the proof and wrote its Lean formalization with AI agents: GPT-6.1 Sol and GPT-6 Astra in Codex, and Claude Opus 5.5 in Claude Code. Plasma AI has reviewed the proof internally. The [blueprint](blueprint/proof.md) states the argument in prose, following the Lean development module by module. `formalization.yaml` records the models and tools used in each phase.

A [companion paper](paper/clique_partitions.pdf) presents the result and outlines the argument, proving the shorter parts and one case of the exclusions in full. The [LaTeX source](paper/clique_partitions.tex) is also available.

**The benchmark.** Densities are normalized by `n²`, so `d = k/n²` lies in `[0, 1/2)`. Write `ε = 1/2 − d` for the limiting density of missing edges (for a graph on `n` vertices, the number of missing edges divided by `n²` is `ε − 1/(2n)`). Then

```
B(d) = d                                   for 0 ≤ d ≤ 1/4,
B(d) = max(W(1/2 − d), E₂(1/2 − d))        for 1/4 < d < 1/2,
B(1/2) = 0.
```

For `d ≤ 1/4`, a bipartite graph with `k` edges has no triangles and needs `k` cliques, so `f(n, k) = k`. Above `1/4`, `W` and `E₂` are built from explicit dual certificates on three families of graphs. A certificate puts charges on the edges that sum to at most `1` over every clique, so its total charge is a lower bound on the number of cliques in any clique partition. Divided by `n²`, the total charges tend to the values below, which show that `f(n, k)` is at least `n² B(k/n²) − o(n²)`:

- *Split graphs*, a clique on `(1 − a)n` vertices joined to an independent set of `an` vertices, with `a = √(2ε)`, have value `H(a) = (2(j + 1)a − (2j + 1)a² − 1) / (j(j + 1))`, where `j = max(1, ⌈(1 − a)/a⌉)`.
- *Mixed graphs* consist of an independent set joined to the disjoint union of an independent set and a clique. `W(ε)` is `H(√(2ε))` for `ε ≤ (51 − 9√21)/100`. Beyond that it is the value of one member of the mixed family, a rational function of a parameter `σ` determined by `ε`, until `σ` reaches the root `σ_d` of `29σ³ − 16σ² − 14σ − 2` in `(1, 11/10)`. After that point `W(ε) = ε`.
- *Two-head graphs* are complete multipartite graphs with two large parts and all other parts of size one. `E₂(ε)` is `H(√(2ε))` up to a threshold `ε_c`, and beyond it the value of one member of the two-head family, a rational function of a parameter `z` determined by `ε`. As `ε` increases from `ε_c` to `1/4`, `z` decreases from the root `z_c` of `−95z⁴ + 18z³ + 193z² − 168z + 40` in `[3/4, 4/5]` to `2/3`.

`Challenge.lean` gives every formula exactly. Let `d₁ = 1/2 − (51 − 9√21)/100 ≈ 0.402`. For `d₁ ≤ d < 1/2`, `W` and `E₂` both equal the split value `H(√(1 − 2d))`. For `1/4 < d < d₁` they are equal at exactly one density, `d_x ≈ 0.384`, and they cross there: `E₂` is larger on `(1/4, d_x)` and `W` on `(d_x, d₁)`. So `B` is the two-head value on `(1/4, d_x]`, the mixed value on `[d_x, d₁]` and the split value on `[d₁, 1/2)`. On `[d₁, 1/2)` it has a kink at `d = κ_k = (1 − 1/k²)/2` for every integer `k ≥ 3` (here `k` indexes the kinks, not edges), and these kinks accumulate at `1/2`.

![The benchmark B on [0, 1/2], colored by the family that attains it](paper/benchmark.svg)

*The benchmark `B`, with the Erdős–Goodman–Pósa bound and the upper bound `(1 − d)/3` of Král', Lidický, Martins and Pehova and of Blumenthal et al. for comparison. `scripts/plot_benchmark.py` computes it numerically from the definitions in `Challenge.lean`; the figure is not checked in Lean.*

## The argument

**Fractional relaxation.** For a graph `G`, let `cp(G)` be the least number of cliques partitioning its edges, and `cp*(G)` the value of its linear relaxation. The largest value of `cp*(G)/n²` over graphs with `n` vertices and `k` edges is `F(k/n²) + o(1)`, uniformly in `k`, for a continuous function `F` on `[0, 1/2]` with `F(d) = d` for `d ≤ 1/4` and `F(1/2) = 0`. The theorem follows from three statements: `F ≥ B`, `F ≤ B`, and `cp(G) ≤ cp*(G) + o(n²)` uniformly over graphs on `n` vertices.

**Lower bound.** Blow-ups of the families above carry explicit feasible solutions of the dual linear program, which certify `F ≥ B`.

**Integer transfer.** The bound `cp(G) ≤ cp*(G) + o(n²)` is the case of Theorem 1.10 of Balogh, He, Krueger, Nguyen and Wigal used here. Lean proves it again, through Szemerédi's regularity lemma, random allocation of clique weights and a hypergraph nibble.

**Upper bound.** Since `F` and `B` are continuous and agree on `[0, 1/4]` and at `1/2`, if `F > B` somewhere then `F − B` has a positive global maximum at some `d` in `(1/4, 1/2)`. Extremal graphs at `d`, with optimal dual charges on their pairs, have limit objects, whose compactness is built on that of graphons through a port of Cameron Freer's Lean proof. One limit is selected by two further extremal choices, and its first and second variations constrain its structure. A separate theorem shows that every complete multipartite limit has dual value at most `B` at its own density. What remains is a short list of possible locations of `d`, and a case analysis excludes each of them. The middle range of `E₂` uses an interval-arithmetic certificate whose 11,882 subtrees of at most 40 boxes are checked in Lean's kernel by `decide +kernel`. So `F ≤ B`.

## Literature and scope

Erdős, Goodman and Pósa ([*The representation of a graph by set intersections*](https://doi.org/10.4153/CJM-1966-014-3), Canad. J. Math. 18 (1966), 106–112) proved `f(n, k) ≤ ⌊n²/4⌋`, using only edges and triangles. Erdős posed the question in *Some unsolved problems in graph theory and combinatorial analysis* (Combinatorial Mathematics and its Applications, Academic Press, 1971, 97–109, item 11 on p. 101), asking whether this bound can be sharpened for `k > n²/4`. Lovász (*On covering of graphs*, Theory of Graphs, 1968, 231–236) treated the covering version, in which the cliques need not be edge-disjoint. For graphs with no `K₄` the question becomes one of packing edge-disjoint triangles, and Győri and Keszegh ([*On the number of edge-disjoint triangles in K₄-free graphs*](https://doi.org/10.1007/s00493-016-3500-0), Combinatorica 37 (2017), 1113–1124) proved that every such graph with `⌊n²/4⌋ + m` edges has `m` edge-disjoint triangles.

For general graphs, write `k = ⌊n²/4⌋ + m`. Győri's theorems on edge-disjoint triangles and cliques (*On the number of edge-disjoint triangles in graphs of given size*, Colloq. Math. Soc. János Bolyai 52 (1988), 267–276, and [*On the number of edge disjoint cliques in graphs of given size*](https://doi.org/10.1007/BF01205075), Combinatorica 11 (1991), 231–243, with a correction in *Edge disjoint cliques in graphs*, Colloq. Math. Soc. János Bolyai 60 (1992), 357–363) give the upper bounds `f(n, k) ≤ ⌊n²/4⌋ − m` when `m` is at most a linear function of `n`, and `f(n, k) ≤ ⌊n²/4⌋ − m + O(m²/n²)` when `m = o(n²)`. Adding a triangle-free graph with `m` edges inside one side of a complete balanced bipartite graph gives a graph with no `K₄` in which every triangle uses one of the added edges; it needs at least `⌊n²/4⌋ − m` cliques, and Győri and Keszegh use these graphs to show that their theorem is sharp. So these bounds determine `f(n, k)` in the first range and up to `O(m²/n²)` in the second. The bound `f(n, k) ≤ n²/4 − m/3 + o(n²)` for all `m` is due to Král', Lidický, Martins and Pehova ([*Decomposing graphs into edges and triangles*](https://doi.org/10.1017/S0963548318000421), Combin. Probab. Comput. 28 (2019), 465–472), whose bound on decompositions into edges and triangles implies it. Blumenthal, Lidický, Pehova, Pfender, Pikhurko and Volec ([*Sharp bounds for decomposing graphs into edges and triangles*](https://doi.org/10.1017/S0963548320000358), Combin. Probab. Comput. 30 (2021), 271–287) sharpened that decomposition bound, which gives `f(n, k) ≤ (n² − k + 2)/3` for large `n`. With the theorem proved here, this bound gives `B(d) ≤ (1 − d)/3`, and numerical evaluation indicates that the inequality is strict for `1/4 < d ≤ 1/2`; neither comparison is checked in Lean. Balogh and Wigal ([*Packing edge disjoint cliques in graphs*](https://doi.org/10.1007/s00493-025-00184-w), Combinatorica 45 (2025)) proved Győri's conjecture that, for each fixed `r ≥ 3`, every graph with `ℓ` more edges than the Turán graph `T_{r−1}(n)` has `(2 − o(1))ℓ/r` edge-disjoint `r`-cliques as `n → ∞`; for `r = 3` this is the result of Král', Lidický, Martins and Pehova, which they prove again by a different method, so for `f(n, k)` it gives the same bound.

Balogh, He, Krueger, Nguyen and Wigal ([*Clique covers and decompositions of cliques of graphs*](https://doi.org/10.19086/aic.2026.9), Advances in Combinatorics 2026:9) compare fractional and integral clique decompositions. The case of their Theorem 1.10 used here, `cp(G) ≤ cp*(G) + o(n²)`, is proved again in this formalization rather than assumed. Concurrent work of Zhang ([*Clique decompositions and covers for large graphs*](https://arxiv.org/abs/2608.25233), arXiv:2608.25233, 2026) also uses linear-programming duality for clique decompositions.

To our knowledge, the formula is new: no earlier work determines `f(n, k)` to within `o(n²)` at any fixed density strictly between `1/4` and `1/2`. The "to our knowledge" novelty claim reflects a targeted search on November 3, 2026 of Bloom's problem entry and its discussion thread, which recorded no proof claims, of `formal-conjectures`, of arXiv, zbMATH Open, Crossref and OpenAlex, and of the web. Besides the bounds above, that search found an AI-generated working report on [Erdős Problem a Day](https://www.erdosproblemaday.com/report/1017) (29 July 2026), not independently verified, that computes `f(n, k)` exactly for `n ≤ 7` and leaves the behavior at positive excess density open. It found no formula for `f(n, k)` at any density above `1/4`.

[`formal-conjectures`](https://github.com/google-deepmind/formal-conjectures/blob/7bdc4a42f24c0316f81c73b26121794b2bed96a3/FormalConjectures/ErdosProblems/1017.lean) states the problem as `erdos_1017.lower_bound` and `erdos_1017.upper_bound`, which ask for natural-number lower and upper bounds on `f(n, k)` for `k > n²/4`, to be supplied as functions of `n` and `k`; this formalization does not supply them. Its definitions of `f` and `IsCliqueEdgePartition` are the ones used here. The estimate here is to within `o(n²)`: just above `n²/4`, where `k − n²/4 = o(n²)`, Győri's bounds above are more precise, and as `k/n²` approaches `1/2`, where `B` tends to `0`, the formula gives only `f(n, k) = o(n²)`.

## Publication layout

`Challenge.lean` states the result using only Mathlib imports. Its `sorry` is deliberate: this file is the statement to be audited, not the proof. The definitions of `f` and `SimpleGraph.IsCliqueEdgePartition` are copied verbatim from [`formal-conjectures`](https://github.com/google-deepmind/formal-conjectures/blob/7bdc4a42f24c0316f81c73b26121794b2bed96a3/FormalConjectures/ErdosProblems/1017.lean) (commit `7bdc4a42f2`), and the benchmark `B` is defined as `benchmark`. The roots `σ_d` and `z_c` and the inverses of the two parametrized families are defined as infima of their exact algebraic solution sets in the stated intervals, so no numerical value enters the statement. `Solution.lean` imports the proof development and supplies the same theorem. `comparator.json` selects `Erdos1017.uniform_asymptotic` and the allowed axioms for [Comparator](https://github.com/leanprover/comparator).

The proof development lives under `Erdos1017/`, grouped into subfolders by part of the proof:

- `Statement.lean`, `Target.lean`, `Benchmark.lean` and `Benchmark/` repeat the `formal-conjectures` definitions with their proved API and define the benchmark. They prove that the infima above are the unique roots and inverses and that `B` is continuous, and they prove the properties of its branches used later.
- `FractionalLimit/` holds the fractional relaxation and its uniform limit `F`.
- `LowerBound/` proves the lower bound `F ≥ B` and the uniform lower bound for `f`.
- `IntegerTransfer/` proves the integer transfer through the regularity cleaning, the random allocation and the hypergraph nibble.
- `Models/` builds the limit models, proves their compactness and selects an optimal model.
- `Multipartite/` proves the multipartite comparison.
- `SelectedModel/` derives the structure of the selected model.
- `ContactLocation/` locates a positive maximum of `F − B`, and `Exclusions/` excludes each location.
- `Certificates/` holds the cover certificate for the middle range of `E₂` and the corner certificates, with the modules that build them. The smaller certificate tables sit with the cases that use them.
- `FullBenchmarkUpper.lean` and `FinalAssembly.lean` combine them into `uniform_asymptotic_proved`, which `Solution.lean` restates as `uniform_asymptotic`.

The certificates are ordinary Lean modules, checked by the kernel. The certificate for the middle range of `E₂` consists of 148 generated piece modules and a root module; the 11,882 subtrees of at most 40 boxes are proved by `decide +kernel` on literal certificate trees and assembled by a covering lemma. `native_decide` is not used anywhere. `scripts/MiddleE2LargeUniversalCertificateCoverGen.lean` generates the cover and `scripts/split_cover_certificate.py` splits it into these modules. The 32 modules `EmptySatCornerHard*.lean`, which are the hard-corner certificate of blueprint §11.3 and the 31 Bernstein chart modules of §10.6 behind it, are proved over the reals by `norm_num` and `ring` and generated by `scripts/corner_certificate/generate_hard_corner.py` from the exact checker `scripts/corner_certificate/hard.py`; `--check` regenerates them and compares them with the repository. Both generators reproduce their modules byte for byte. To check this, run `lake env lean scripts/MiddleE2LargeUniversalCertificateCoverGen.lean` on a built library (about seven minutes and 1.1 GB of memory) and then `python3 scripts/split_cover_certificate.py --check`, and run `python3 scripts/corner_certificate/generate_hard_corner.py --check` (one to two seconds, Python 3.9 or later). The Python scripts use only the standard library. The smaller certificate tables are written directly in their Lean files and checked by Lean like the rest of the proof.

`vendor/Graphon/` holds the import closure of `Graphon.Compactness`, 11 modules, from Cameron Freer's [graphon](https://github.com/cameronfreer/graphon) library at commit `9f7be59fa754d260a544b4cfd83d6a5b94f7552e`, under its upstream module names and its Apache 2.0 license (`vendor/Graphon/LICENSE`). The port to this toolchain leaves the mathematical statements unchanged. It removes the blueprint annotations, converts the files to the module system, adapts proofs to renamed Mathlib lemmas, and makes two declarations public: the definition `energyRect` and the lemma `exists_cutNormDiff_limit_of_summable`. The compactness of the limit models is proved from it under `Erdos1017/`. [`vendor/Graphon/README.md`](vendor/Graphon/README.md) records the provenance and every change.

`blueprint/` states the argument for the compared theorem in prose, following the Lean development module by module, starting from `blueprint/proof.md`. It proves some steps and cases in full and summarizes the others, naming their Lean declarations. The Lean development is the proof of record.

Every Lean file of the library, the vendored library included, uses the module system: it begins with `module`, imports with `public import`, and exposes its definitions with `@[expose] public section`. The one exception to the imports is `Erdos1017/IntegerTransfer/FixedDensityCleaning.lean`, which also imports two Mathlib modules privately with a plain `import`. No file imports all of Mathlib.

`paper/` holds the companion paper: its source `clique_partitions.tex`, the compiled [`clique_partitions.pdf`](paper/clique_partitions.pdf), the figure `benchmark.pdf`, and `benchmark.svg`, the figure of `B` in this README, which `python3 scripts/plot_benchmark.py` draws from the definitions in `Challenge.lean`.

`formalization.yaml` records the mathematical sources, authorship, AI use, source fidelity, and review status for a registry submission.

`scripts/` also holds the checks of the [Palomar template](https://github.com/PalomarRegistry/PalomarTemplate), unchanged: `check-lean-sources.py` checks the module headers and the 10,000-line limit, `validate-formalization.rb` checks `formalization.yaml`, and `verify-comparator.sh` runs the toolchain's `lake comparator` with its bundled NanoDa and con-ron kernels (it needs Linux and `bwrap`). Palomar registers only NanoDa with `lake comparator` and replays con-ron afterwards as a separate, advisory check.

The Lean and Mathlib versions are fixed by `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`.

```sh
lake exe cache get
lake build
```

The full build includes `Challenge` and therefore reports its intentional `sorry` warning. The proof in `Solution` can also be built directly with `lake build Solution`.

The certificate modules make the full build memory-intensive. Lake runs one `lean` process per worker thread, so cap the thread count to fit the available memory, for example with `LEAN_NUM_THREADS=4 lake build`. With `LEAN_NUM_THREADS=4`, a full build from a fresh clone, after `lake exe cache get`, took 68 minutes on an Apple silicon Mac with 32 GB of memory, and the combined memory of its `lean` and `lake` processes peaked at about 10 GB.
