# Blueprint: uniform asymptotics of clique partition numbers

This document states in prose the argument for the theorem that Comparator
checks, following the Lean development module by module. Each section names
the modules and the Lean declarations it describes. It proves some steps and
cases in full and summarizes the others; the Lean development is the proof
of record. Plasma AI found the proof and wrote its Lean formalization with
AI agents: GPT-6.1 Sol and GPT-6 Astra in Codex, and Claude Opus 5.5 in
Claude Code. Inputs from earlier work are credited below.
`formalization.yaml` records the models and tools used in each phase.

The definitions of the problem (`Erdos1017/Statement.lean`, restated in
`Challenge.lean`) are copied verbatim from `formal-conjectures`, revision
`7bdc4a42`, with local additions marked. The graphon library in
`vendor/Graphon/` is Cameron Freer's, revision `9f7be59`, ported to Lean
v4.35.0-rc4. Neither is an extra hypothesis.

The blueprint has four files. This one holds the statement and its final
assembly, the benchmark, the fractional limit, the lower bound, the integer
transfer, the limit models, the multipartite comparison and the location of
a positive maximum (§0 to §7, §9), and short summaries of the other three:
`selected_model.md` (§8, the structure of the selected model),
`exclusions.md` (§10, the exclusions) and `certificates.md` (§11, the
kernel-checked certificates). The module lists of each section leave out the
ten certificate modules of §11.4, which sit in the folders of the sections
that use them.

**Shape of the proof.** B is the benchmark of §2. The fractional density limit
F(d) of §3 is the supremum of 0 and of cp*(G)/N² − 3·abs(e(G)/N² − d) over all
graphs G on N ≥ 1 vertices, where cp* is the linear relaxation of the clique
partition number. F ≥ B comes from explicit blow-ups carrying feasible dual
charges (§4). F ≤ B is proved by contradiction: if F > B somewhere, F − B has
a positive global maximum at some d ∈ (1/4, 1/2), and compactness gives an
optimal limit model at d, selected by two further extremal choices (§6). Its
structure (§8), with the theorem that multipartite profiles lie below B (§7),
forces d to be a remaining contact (§9): an E₂ point, the W/E₂ corner or a
reciprocal cusp. Splitting the E₂ points into three ranges of their parameter
gives five contact types, each excluded in §10, the middle E₂ range with a
kernel-checked certificate (§11); a sixth exclusion, of smooth W points, is
used inside §9. The same-graph transfer cp ≤ cp* + o(n²) (§5) and the uniform
limit of f*/n² (§3) then give the theorem (§1).

---

## 0. Conventions and notation

No modules.

**Conventions.** Module paths are relative to the repository root.
Declarations are in namespace `Erdos1017` or `Erdos1017.CappedModel`, and are
cited fully qualified where a section introduces them; the running text may
shorten them. `S` abbreviates `Erdos1017.CappedModel.SelectedHighLowStructure`
in Lean names; in the text S is the selected structure of §8. Statements about
kernels hold μ×μ-almost everywhere unless stated pointwise; "null" means of
measure zero and "positive" of positive measure. Displayed formulas are
indented blocks in plain Unicode.

**Sign convention.** Lean's multiplier is m ∈ [−3, 1] and its shifted kernel
is M = Y − mG. The text writes ℓ = −m, so M = Y + ℓG and ℓ > 0 at every model
that matters (§8.3). Every inequality copied from Lean is rewritten in ℓ: a
hypothesis −m < 1 reads ℓ < 1, the factor 1 + m reads 1 − ℓ, and the
conclusion −m ∈ (2 − 2/k − 2/(k+1), 2 − 2/k) of
`Erdos1017.CappedModel.FullStationaryClass.split_cusp_strict_slope` reads
ℓ ∈ (L_k, U_k).

**The problem.**

| Symbol | Meaning | Lean |
|---|---|---|
| n, k, d | vertices, edges, density d = k/n² ∈ [0, 1/2), normalized by n² | `Erdos1017.uniform_asymptotic` |
| η | tolerance in uniform statements (the main theorem's ε, §1) | |
| cp(G), cp*(G) | clique partition number and its linear relaxation (§3) | `Erdos1017.cliquePartitionNumber`, `Erdos1017.FractionalGraph.value` |
| f(n,k), f*(n,k) | maxima of cp, cp* over graphs with n vertices and k edges | `Erdos1017.f`, `Erdos1017.FractionalGraph.extremal` |
| F(d) | fractional density limit, a penalized supremum over finite graphs (§3) | `Erdos1017.FractionalGraph.densityLimit` |

**The benchmark** (§2).

| Symbol | Meaning | Lean |
|---|---|---|
| ε, h, r | ε = 1/2 − d, h = 1 − 2d = 2ε, r = √(1 − 2d) | Lean's variable `e` is ε |
| B(d) | d for d ≤ 1/4; max(W(ε), E₂(ε)) for 1/4 < d < 1/2; 0 for d ≥ 1/2 | `Erdos1017.benchmark` |
| split branch | value (−(2j+1)r² + 2(j+1)r − 1)/(j(j+1)), j = max(1, ⌈(1 − r)/r⌉) | `Erdos1017.Benchmark.splitValue` |
| W, E₂ | the mixed and the two-head curves | `Erdos1017.Benchmark.mixedCurve`, `Erdos1017.Benchmark.twoHeadCurve` |
| ε*, ε_C, ε_x, ε_D | W/split junction, start of the E₂ branch, W/E₂ crossing, end of the W branch; ε* < 1/10 < ε_C < ε_x < 1/8 < ε_D < 1/4 | `Erdos1017.Benchmark.epsilonStar`, `Erdos1017.Benchmark.epsilonC`, `Erdos1017.Benchmark.epsilonD` |
| σ₀, σ_D, z_C | W parameter at ε*, W root, E₂ root | `Erdos1017.Benchmark.sigmaZero`, `Erdos1017.Benchmark.sigmaD`, `Erdos1017.Benchmark.zC` |
| q | E₂ parameter q = 3z − 2, z the two-head parameter; at an E₂ contact 0 < q < 213/1000 | |
| R(q), ℓ(q), h(q), g(q) | the E₂ denominator 1 + 7q + q², slope (2 − q)/(2 + q), missing density (q + 2)²(1 + 4q + 13q²)/(8R(q)²), floor q(1 + 2q)/(2R(q)) for γ | `Erdos1017.LowerE2Scalar.denominator`, `Erdos1017.LowerE2Scalar.multiplier`, `Erdos1017.LowerE2Scalar.missingMass`, `Erdos1017.LowerE2Scalar.gapFloor` |
| k | cusp index: r = 1/k, d = (1 − 1/k²)/2, k ≥ 3 | |
| contact | the density of a positive maximum of F − B, with the branch of B there (§9) | `Erdos1017.CappedModel.RemainingBenchmarkContact` |

**Limit models** (§6).

| Symbol | Meaning | Lean |
|---|---|---|
| (Ω, μ, W) | probability space with a random-color kernel: each pair is absent, or present with a charge in [−3, 1] | `Erdos1017.CappedModel.Model` |
| G, Y | mean adjacency and mean charge of a pair | `Erdos1017.CappedModel.adjacencyKernel`, `Erdos1017.CappedModel.chargeKernel` |
| d, c | density (1/2)∫∫G and objective (1/2)∫∫Y; c = F(d) at the selected model | `Erdos1017.CappedModel.density`, `Erdos1017.CappedModel.objective` |
| fully feasible | every sampled clique of every order has total charge at most 1, almost surely | `Erdos1017.CappedModel.FullFeasible` |
| m, ℓ, M | Lean's multiplier, ℓ = −m, shifted kernel M = Y + ℓG | `Erdos1017.CappedModel.shiftedKernel` |
| ν, γ, δ | row constant ν = 2(c + ℓd), intercept γ = ν − ℓ = 2c − ℓh, δ = 1 − ℓ | |
| class | the stationary class at (d, c): M ∈ [0, 4], (1 − G)M = 0, constant rows ν, positive index at most 2 | `Erdos1017.CappedModel.FullStationaryClass` |
| selected model | class member at a positive global maximum of F − B with m minimal, then J = ∫∫M² maximal (§6) | `Erdos1017.CappedModel.exists_selected_full_positive_global_excess` |
| strict gap | c > B(d) | |

**The selected model** (§8).

| Symbol | Meaning | Lean |
|---|---|---|
| whole atom I_r, A_r | a positive set of points with one M row and no internal edges; A_r its mass | `Erdos1017.CappedModel.SelectedHighLowStructure.originalAtomMass` |
| D | clique dust: the complement of the atoms, complete | field `D` of `Erdos1017.CappedModel.SelectedHighLowStructure` |
| HIGH, LOW, NEUTRAL | ends of outside missing pairs (M = 0, different rows), HIGH the end of larger degree; NEUTRAL has none | `Erdos1017.OrderedZeroRelation.highClass`, `Erdos1017.OrderedZeroRelation.lowClass`, `Erdos1017.OrderedZeroRelation.neutralClass` |
| universal atom | an atom joined to every point outside its own fiber; exactly the NEUTRAL atoms | `Erdos1017.CappedModel.SelectedHighLowStructure.neutral_atom_adjacency` |
| peak, A | the atom that is the largest part of every forward-flow endpoint, and its mass | `Erdos1017.CappedModel.SelectedHighLowStructure.IsCommonForwardPeak` |
| plateau P, height t | LOW or NEUTRAL atoms receiving the largest recovered mass t in the reverse recovery | `Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.plateau` |
| S_P, b | compulsory source of the plateau; b the mass of a one-atom plateau, t = b + μ(S_P) | `Erdos1017.CappedModel.SelectedHighLowStructure.reverseCompulsorySource` |
| saturated pair | two atoms with charge 1 between them; unique when it exists | `Erdos1017.CappedModel.SelectedHighLowStructure.IsSaturatedAtomPair` |
| N(r) | points outside I_r joined to it | `Erdos1017.CappedModel.SelectedHighLowStructure.rootNeighborhood` |
| body energy | ∫∫ max(Y, 0)² over (Ω \ I)², for a set I (usually an atom); "zero body" when it vanishes | `Erdos1017.PhysicalPrimal.bodyPositiveEnergy` |
| y | deficit ratio 1 − 2γ/δ; a universal saturated peak has A ≤ y | `Erdos1017.CappedModel.SelectedHighLowStructure.universal_atom_mass_le_saturated_deficit_ratio` |
| physical | realized by points and finite cliques of Ω, as opposed to moments | |

The reverse recovery has no letter in the text; Lean names it `R`. One letter
has two uses that the context separates: N is the NEUTRAL class and N(r) a
neighbourhood. "Part" is a part of a multipartite profile (§4, §7); "head" is
an atom of a plateau or a saturated pair (§10).

---

## 1. The statement and the final assembly

`Challenge.lean`, `Erdos1017/FinalAssembly.lean`, `Erdos1017/FullBenchmarkUpper.lean`, `Solution.lean`, `Erdos1017/Statement.lean`, `Erdos1017/Target.lean`.

- **The theorem** (`Erdos1017.uniform_asymptotic`). In Lean:

      theorem uniform_asymptotic :
          ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
            ∀ k : ℕ, k ≤ n.choose 2 →
              |(f n k : ℝ) / (n : ℝ) ^ 2 - benchmark ((k : ℝ) / (n : ℝ) ^ 2)| < ε

  Here, and only here, ε is the tolerance; elsewhere the tolerance is η and
  ε = 1/2 − d. The estimate is additive, uniform over all feasible edge
  counts, and has no rate. Both f and the density are normalized by n², so
  k/n² ≤ (n − 1)/(2n) < 1/2.
- **Clique edge partitions** (`SimpleGraph.IsCliqueEdgePartition`). A finite
  family of vertex sets, each with at least two vertices and a clique of G,
  such that every edge of G lies in exactly one member.
- **The extremal function** (`Erdos1017.f`). f(n,k) is the least m such that
  every graph on {0, …, n − 1} with exactly k edges has a clique edge
  partition with at most m members. For k > C(n,2) there is no such graph,
  so the condition holds vacuously and f(n,k) = 0.
- **The partition number** (`Erdos1017.cliquePartitionNumber`). cp(G) is the
  least size of a clique edge partition of G. By
  `Erdos1017.f_le_iff_cliquePartitionNumber`, f(n,k) ≤ m exactly when
  cp(G) ≤ m for all such G, so f(n,k) = max cp(G) for k ≤ C(n,2).
- **The trusted statement.** `Challenge.lean` imports only Mathlib and
  restates clique edge partitions and f, copied from `formal-conjectures` and
  identical to `Erdos1017/Statement.lean`, and B with its auxiliary definitions,
  identical to `Erdos1017/Benchmark.lean` (§2). Comparator checks that
  `Erdos1017.uniform_asymptotic` of `Solution.lean` proves that exact
  statement with the axioms propext, Quot.sound and Classical.choice only;
  it is the only target. `Erdos1017.UniformAsymptotic` (`Erdos1017/Target.lean`) is the
  same proposition as a definition, proved by
  `Erdos1017.uniform_asymptotic_proved`, and `uniform_asymptotic` is that
  proof.
- **Final assembly** (`Erdos1017.uniform_asymptotic_proved`,
  `Erdos1017.uniformAsymptotic_of_cover`).
  `uniform_asymptotic_proved` is `uniformAsymptotic_of_cover` applied to the
  kernel-checked fact `Erdos1017.MiddleE2LargeUniversal.FixedPoint.cover_root`
  (cover 80 IBox.root = true, §11), and `uniformAsymptotic_of_cover h` is
  `Erdos1017.finalUniformAsymptotic` applied to
  `Erdos1017.densityLimit_le_benchmark_of_cover h`. `Erdos1017/FinalAssembly.lean`
  also states the unconditional bound F ≤ B on [0, 1/2] separately.
- **Conditional assembly** (`Erdos1017.finalUniformAsymptotic`). If
  F(d) ≤ B(d) for every d ∈ [0, 1/2], the theorem holds.
  - Let η > 0. There are N₁ with f(n,k) ≤ f*(n,k) + (η/3)n² for n ≥ N₁ and
    all k (`Erdos1017.exists_integer_extremal_upper_transfer`, §5); N₂ with
    abs(f*(n,k)/n² − F(k/n²)) < η/3 for n ≥ N₂ and k ≤ C(n,2)
    (`Erdos1017.FractionalGraph.extremal_uniform_convergence`, §3); and N₃
    with f(n,k)/n² > B(k/n²) − η for n ≥ N₃ and k ≤ C(n,2)
    (`Erdos1017.benchmark_uniform_integer_lower`, §4).
  - For n ≥ max(N₁, N₂, N₃) and k ≤ C(n,2), d = k/n² ∈ [0, 1/2]
    (`Erdos1017.normalized_edge_count_mem_density_interval`) and

        B(d) − η < f(n,k)/n² ≤ f*(n,k)/n² + η/3 < F(d) + 2η/3 ≤ B(d) + 2η/3.

- **The upper bound** (`Erdos1017.densityLimit_le_benchmark_of_cover`). If
  cover 80 IBox.root = true, then F(d) ≤ B(d) for every d ∈ [0, 1/2].
  - Suppose F(d₀) > B(d₀) for some d₀ ∈ [0, 1/2]. Take Ω = [0, 1] with
    Lebesgue measure: compact metric, standard Borel, atomless, with
    separable L². `Erdos1017.CappedModel.exists_selected_remaining_contact`
    (§9) gives d ∈ (1/4, 1/2), a model W and a multiplier m in the
    stationary class at (d, F(d)) (§6), with B(d) < c = F(d), with
    objective − B(density) maximal at W among all fully feasible models on
    Ω under every probability law, a selected structure S (§8), and one of
    three remaining contacts. Strict split cells, the W/split junction and
    smooth W points are already excluded inside that theorem (§9, §10.1).
  - The contact is dispatched by the tree below, the map of the whole upper
    bound; every leaf proves False. An E₂ contact supplies
    q ∈ (0, 213/1000), d = (1 − h(q))/2, B(d) = twoHeadValue((q + 2)/3) and
    B′(d) = −ℓ(q) (§2). The lower leaf uses q and d only; the middle and
    upper leaves also receive the value and derivative of B. The corner leaf
    receives ε ∈ [ε_C, ε_D] and the equality of the curves, the cusp leaf k
    and d. Only the middle leaf uses the cover premise, which `cover_root`
    discharges.

| Contact | Condition | Leaf | Section |
|---|---|---|---|
| E₂, lower | 0 < q ≤ 1/10 | `Erdos1017.CappedModel.SelectedHighLowStructure.no_lowerE2_contact` | §10.2 |
| E₂, middle | 1/10 < q < 1/5 | `Erdos1017.CappedModel.SelectedHighLowStructure.no_middle_e2_contact_of_cover` | §10.4 |
| E₂, upper | 1/5 ≤ q < 213/1000 | `Erdos1017.CappedModel.SelectedHighLowStructure.no_upperE2_contact` | §10.3 |
| W/E₂ corner | ε_C < ε < ε_D, W(ε) = E₂(ε) | `Erdos1017.CappedModel.SelectedHighLowStructure.no_corner_global_excess` | §10.6 |
| reciprocal cusp | d = (1 − 1/k²)/2, k ≥ 3 | `Erdos1017.CappedModel.SelectedHighLowStructure.no_cusp_contact` | §10.5 |

---

## 2. The benchmark B

`Erdos1017/Benchmark.lean`, `Erdos1017/Benchmark/BenchmarkContactAlternatives.lean`, `Erdos1017/Benchmark/BenchmarkContactGeometry.lean`, `Erdos1017/Benchmark/BenchmarkContinuity.lean`, `Erdos1017/Benchmark/BenchmarkCrossingBounds.lean`, `Erdos1017/Benchmark/BenchmarkDenseHeadCountGuards.lean`, `Erdos1017/Benchmark/BenchmarkE2Activity.lean`, `Erdos1017/Benchmark/BenchmarkFamilyGuards.lean`, `Erdos1017/Benchmark/BenchmarkHeadCountGuards.lean`, `Erdos1017/Benchmark/BenchmarkHeadRatio.lean`, `Erdos1017/Benchmark/BenchmarkPhiBounds.lean`, `Erdos1017/Benchmark/BenchmarkProperties.lean`, `Erdos1017/Benchmark/SplitCurve.lean`.

Erdős, Goodman and Pósa proved f(n,k) ≤ ⌊n²/4⌋; below density 1/4
triangle-free graphs give F(d) = d (§4). Above 1/4, B is the larger of two
curves in ε = 1/2 − d, built on each range from the dual value of a family
of blow-ups optimized over its part sizes (§4): split graphs (a clique
joined to an independent set), W graphs (Lean: mixed) and E₂ graphs (Lean:
two-head).

- **Definition** (`Erdos1017.benchmark`, `Erdos1017.benchmark_of_le_quarter`,
  `Erdos1017.benchmark_half`). B(d) = d for d ≤ 1/4,
  B(d) = max(W(ε), E₂(ε)) for 1/4 < d < 1/2, and B(d) = 0 for d ≥ 1/2.
- **Split branch** (`Erdos1017.Benchmark.splitValue`). For 0 < r ≤ 1 let
  j = max(1, ⌈(1 − r)/r⌉), so 1/(j + 1) ≤ r < 1/j when r < 1, and

      splitValue(r) = (−(2j + 1)r² + 2(j + 1)r − 1)/(j(j + 1)),   splitValue(0) = 0.

  A split cell is 1/(j + 1) < r < 1/j. At r = 1/k (k ≥ 2), j = k − 1 and
  splitValue(1/k) = ((k − 1)²/k²)/(k(k − 1)) = (k − 1)/k³
  (`Erdos1017.Benchmark.splitValue_reciprocal`). Minus the one-sided slopes
  of B there are U_k = 2 − 2/k < 2 and L_k = 2 − 2/k − 2/(k + 1) (§9), with
  L_k ≥ 11/10 for k ≥ 4 (`Erdos1017.Benchmark.split_cusp_upper_slope_lt_two`,
  `Erdos1017.Benchmark.split_cusp_lower_slope_ge_eleven_tenths`).
- **W branch** (`Erdos1017.Benchmark.mixedCurve`, `Erdos1017.Benchmark.mixedValue`,
  `Erdos1017.Benchmark.epsilonStar`). With σ₀ = (3 + √21)/6, ε* = (51 − 9√21)/100:

      mixedDensity(s) = (2 + 16s + 33s² − 15s⁴)/(2(s² + 8s + 2)²),
      mixedValue(s)   = (6 + 46s + 85s² − 16s³ − 16s⁴)/(6(s² + 8s + 2)²),
      W(ε) = splitValue(√(2ε)) (ε ≤ ε*),  mixedValue(mixedInverse ε) (ε* < ε ≤ ε_D),
             ε (ε > ε_D),

  where σ_D is the infimum of the roots of 29s³ − 16s² − 14s − 2 in
  [1, 11/10], ε_D = mixedDensity(σ_D), and mixedInverse(ε) is the infimum of
  the solutions of mixedDensity(s) = ε in [σ_D, σ₀].
- **E₂ branch** (`Erdos1017.Benchmark.twoHeadCurve`, `Erdos1017.Benchmark.twoHeadValue`).

      twoHeadDensity(z) = z²(13z² − 16z + 5)/(16(z² + z − 1)²),
      twoHeadValue(z)   = twoHeadDensity(z) + (3z − 2)²(1 − z)(3z − 1)/(24(z² + z − 1)²),
      E₂(0) = 0,  E₂(ε) = splitValue(√(2ε)) (0 < ε ≤ ε_C),
             twoHeadValue(twoHeadInverse ε) (ε > ε_C),

  where z_C is the infimum of the roots of
  P_C(z) = −95z⁴ + 18z³ + 193z² − 168z + 40 in [3/4, 4/5],
  ε_C = twoHeadDensity(z_C), and twoHeadInverse(ε) is the infimum of the
  solutions of twoHeadDensity(z) = ε in [2/3, z_C].
- **The infima are the unique solutions** (`Erdos1017.Benchmark.sigmaD_spec`,
  `Erdos1017.Benchmark.zC_spec`, `Erdos1017.Benchmark.mixedInverse_spec`,
  `Erdos1017.Benchmark.twoHeadInverse_spec`). A closed nonempty set bounded
  below contains its infimum. The W polynomial, −3 at 1 and 1839/1000 at
  11/10, is 29(s − 1)³ + 71(s − 1)² + 41(s − 1) − 3; P_C, 25/256 at 3/4 and
  −72/125 at 4/5, is 25/256 − (135/16)u − (697/8)u² − 267u³ − 95u⁴ with
  u = z − 3/4. mixedDensity′(s) = −s(2 + 24s + 93s² + 120s³)/(s² + 8s + 2)³
  and twoHeadDensity′(z) = z(21z³ − 39z² + 24z − 5)/(8(z² + z − 1)³) are
  negative on the intervals, mixedDensity(σ₀) = ε* (in ℚ(√21)) and
  twoHeadDensity(2/3) = 1/4. By the intermediate value theorem and strict
  monotonicity each equation has exactly one solution in its interval; so
  mixedInverse(ε*) = σ₀ and twoHeadInverse(ε_C) = z_C.
- **Branch identities** (`Erdos1017.Benchmark.mixed_branch_match`,
  `Erdos1017.Benchmark.twoHead_branch_match`).
  - At ε*: √(2ε*) = (9 − √21)/10 ∈ [1/3, 1/2), so j = 2 and
    splitValue(r) = (−5r² + 6r − 1)/6, which equals mixedValue(σ₀) by
    computation in ℚ(√21).
  - At ε_D: mixedValue(s) − mixedDensity(s) =
    s(29s³ − 16s² − 14s − 2)/(6(s² + 8s + 2)²) vanishes at σ_D
    (`Erdos1017.Benchmark.mixedValue_sigmaD`).
  - At ε_C: with V = twoHeadValue(z) and e = twoHeadDensity(z),
    (V + 5e/3 + 1/6)² − 2e = z²(z − 1)²P_C(z)/(576(z² + z − 1)⁴) vanishes at
    z_C, so V + 5ε_C/3 + 1/6 = √(2ε_C) as V ≥ 0. As ε_C ∈ [13/121, 9/80],
    r = √(2ε_C) ∈ [1/3, 1/2) and splitValue(r) = r − 5ε_C/3 − 1/6 = V.
  - At ε = 1/4: twoHeadValue(2/3) = 1/4 = B(1/4).
- **Continuity** (`Erdos1017.benchmark_continuousOn`). On [0, 1/2], from
  continuity of each piece, agreement of adjacent split polynomials at
  r = 1/(j + 1), splitValue(r) → 0 as r → 0, and the identities above.
- **Constants, crossing and alternatives** (`Erdos1017.Benchmark.epsilonStar_lt_tenth`
  and its companions, `Erdos1017.Benchmark.exists_unique_crossing_on_overlap`,
  `Erdos1017.Benchmark.family_contact_alternatives`). On [ε_C, ε_D], E₂ − W
  increases strictly and changes sign in (23243416, 23243417)/(2·10⁸), so
  the curves cross once, at ε_x; ε* < 1/10 < ε_C < 9/80 < ε_x < 1/8 < ε_D
  (numerically 0.0976, 0.1104, 0.1162, 0.1367; d ≈ 0.4024, 0.3896, 0.3838,
  0.3633). For ε* < ε < 1/4: W strictly wins (ε < ε_D), E₂ strictly wins
  (ε > ε_C), or the curves are equal (ε_C < ε < ε_D).
- **E₂ contacts** (`Erdos1017.Benchmark.strict_twoHead_contact_parameters`,
  `Erdos1017.Benchmark.active_twoHead_parameter_lt_cutoff`,
  `Erdos1017.Benchmark.benchmark_e2_q`). If 1/4 < d < 1/2, ε > ε_C and E₂
  strictly wins, then q = 3·twoHeadInverse(ε) − 2 ∈ (0, 213/1000) (z > 2/3
  as twoHeadDensity(2/3) = 1/4 ≠ ε; z < 2213/3000 because E₂ − W is
  increasing and negative at the left end of the crossing box, so
  ε > 23243416/(2·10⁸) > twoHeadDensity(2213/3000)), d = (1 − h(q))/2,
  B(d) = twoHeadValue((q + 2)/3), and B′(d) = −ℓ(q), since near d, B = E₂
  has ε-derivative (4 − 3z)/(3z) = ℓ(q).
  Conversely B((1 − h(q))/2) = twoHeadValue((q + 2)/3) for 0 < q ≤ 1/5.
- **E₂ scalars** (`Erdos1017.LowerE2Scalar.denominator`,
  `Erdos1017.LowerE2Scalar.multiplier`, `Erdos1017.LowerE2Scalar.missingMass`,
  `Erdos1017.LowerE2Scalar.gapFloor`).

      R(q) = 1 + 7q + q²,   ℓ(q) = (2 − q)/(2 + q),
      h(q) = (q + 2)²(1 + 4q + 13q²)/(8R(q)²),   g(q) = q(1 + 2q)/(2R(q)).

  (R(q) always carries its argument; the reverse recovery of §8 has no
  letter in the text.)

  As z² + z − 1 = R(q)/9 at z = (q + 2)/3, h(q) = 2·twoHeadDensity(z) and
  g(q) = 2·twoHeadValue(z) − ℓ(q)h(q)
  (`Erdos1017.LowerE2Scalar.gapFloor_eq_twoHeadValue`): at an E₂ contact
  with c > B(d), γ = 2c − ℓh > g(q).
- **Guards** (`Erdos1017.Benchmark.active_mixed_parameter_guards`,
  `Erdos1017.Benchmark.benchmark_head_count_guards`). Where W ≥ E₂ on
  [ε*, ε_D]: W parameter > 7/6 and 2ε < 1163/5000 (for §10.1). For
  3/8 < d < 21/50: B has right derivative −L, 1/2 < L < 1, B(d) > 1/2 − d and
  √(1 − 2d)(1 − L)/(2(B(d) − L(1/2 − d))) < 2 (for §7).

---

## 3. The fractional value and the density limit

`Erdos1017/FractionalLimit/FinitePrimal.lean`, `Erdos1017/FractionalLimit/FractionalDensityLimit.lean`, `Erdos1017/FractionalLimit/FractionalExtremal.lean`, `Erdos1017/FractionalLimit/FractionalGraph.lean`, `Erdos1017/FractionalLimit/FractionalGraphBlowup.lean`, `Erdos1017/FractionalLimit/FractionalGraphChanges.lean`, `Erdos1017/FractionalLimit/FractionalGraphCounts.lean`, `Erdos1017/FractionalLimit/FractionalGraphDelete.lean`, `Erdos1017/FractionalLimit/FractionalGraphEdit.lean`, `Erdos1017/FractionalLimit/FractionalGraphEmbedding.lean`, `Erdos1017/FractionalLimit/FractionalGraphProjection.lean`, `Erdos1017/FractionalLimit/FractionalLimitFoundation.lean`, `Erdos1017/FractionalLimit/FractionalUniformLimit.lean`, `Erdos1017/FractionalLimit/Selector.lean`.

- **The relaxation** (`Erdos1017.FractionalGraph.Clique`,
  `Erdos1017.FractionalGraph.Feasible`, `Erdos1017.FractionalGraph.value`).
  A weighting w ≥ 0 of the cliques with at least two vertices is feasible
  when every edge has load exactly one; cp*(G) is the least total weight. The
  LP is finite and attained, also for the edgeless graph
  (`Erdos1017.FractionalGraph.exists_optimal`). A clique edge partition with
  unit weights is feasible, so cp* ≤ cp
  (`Erdos1017.FractionalGraph.value_le_cliquePartitionNumber`), and the edges
  give cp*(G) ≤ e(G).
- **Blow-ups** (`Erdos1017.FractionalGraph.value_blowup`). Replacing each
  vertex by t independent clones multiplies cp* by t². Upper bound: spread
  w_S uniformly over the t^|S| transversals of S, each with weight
  w_S t^(2 − |S|); a clone edge over xy lies in t^(|S| − 2) transversals of
  each S ∋ x, y, so its load is one, and the total is t²Σw_S. Lower bound:
  clones are independent, so a clique of the blow-up projects injectively to
  a clique of G; the projection of a feasible weighting loads each edge of G
  with t², and dividing by t² gives a feasible weighting of G. Relabelling and
  isolated vertices do not change cp* (`Erdos1017.FractionalGraph.value_map`).
- **Edits** (`Erdos1017.FractionalGraph.value_add_edge_le`,
  `Erdos1017.FractionalGraph.value_delete_edge_le`,
  `Erdos1017.FractionalGraph.value_le_edit_cost`).
  - Adding an absent edge uv costs at most 1: give {u, v} weight 1.
  - Deleting an edge uv costs at most 3. In an optimal w keep the cliques not
    containing both u and v, and replace each S ⊇ {u, v} by a random subset T:
    exactly one of u, v, each with probability 1/2, and every other vertex of S
    independently with probability 1/2; T gets weight 4w_S P(T) (T with fewer
    than two vertices is dropped). T is a clique of G − uv, and every other
    pair of S has load 4·(1/2)(1/2)w_S = w_S
    (`Erdos1017.FractionalGraph.repair_pair_expectation`). The extra cost is
    3Σ_{S ∋ u,v} w_S = 3.
  - Iterating: cp*(H) ≤ cp*(G) + 3·#(E(G) ∖ E(H)) + #(E(H) ∖ E(G)).
  - These constants give the charge range [−3, 1] of §6. By finite LP
    duality every graph has an optimal dual charge y, of value cp*(G), and
    every optimal y has entries in [−3, 1]
    (`Erdos1017.FractionalGraph.exists_bounded_dual`,
    `Erdos1017.WeightedGraph.optimal_dual_mem_Icc`): y_uv ≤ 1 is the test on
    {u, v}, and setting y_uv = 0 gives a dual of G − uv, so by weak duality
    cp*(G) − y_uv ≤ cp*(G − uv) ≤ cp*(G) + 3.
- **The fractional extremum** (`Erdos1017.FractionalGraph.extremal`,
  `Erdos1017.FractionalGraph.extremal_edit_bounds`). f*(n,k) is the attained
  maximum of cp* over k-edge graphs (0 if k > C(n,2)). For
  k₁ ≤ k₂ ≤ C(n,2), f*(n,k₂) ≤ f*(n,k₁) + (k₂ − k₁) and
  f*(n,k₁) ≤ f*(n,k₂) + 3(k₂ − k₁), by editing an extremal graph; likewise
  cp*(H) ≤ f*(n,k) + 3·abs(e(H) − k)
  (`Erdos1017.FractionalGraph.value_le_extremal_edit`).
- **The density limit** (`Erdos1017.FractionalGraph.densityCandidates`,
  `Erdos1017.FractionalGraph.densityLimit`,
  `Erdos1017.FractionalGraph.finite_graph_le_densityLimit`). F(d) is the
  supremum of 0 and of cp*(G)/N² − 3·abs(e(G)/N² − d) over all graphs G on
  N ≥ 1 vertices (each at most 1). F is a penalized supremum, not a limit by
  definition; the limit is the theorem below.
- **Lipschitz bound** (`Erdos1017.FractionalGraph.densityLimit_lipschitz`).
  A candidate at d is at most the same graph's candidate at d′ plus
  3·abs(d − d′), and F ≥ 0; so F is 3-Lipschitz.
- **The limit** (`Erdos1017.FractionalGraph.tendsto_extremal_of_density`,
  `Erdos1017.FractionalGraph.finite_graph_eventual_lower_along`). If k_n ≤ C(n,2)
  and k_n/n² → d, then f*(n,k_n)/n² → F(d).
  - Upper: an extremal graph is a candidate, so
    f*(n,k_n)/n² ≤ F(d) + 3·abs(k_n/n² − d).
  - Lower: let a < F(d) and take a candidate above a; if it is 0 use f* ≥ 0.
    Otherwise it comes from a graph G on N vertices, which is now fixed while
    n → ∞. The padded blow-up H_n (⌊n/N⌋ clones per vertex, the rest
    isolated) has cp*(H_n) = ⌊n/N⌋²cp*(G) and e(H_n) = ⌊n/N⌋²e(G), so

        f*(n,k_n)/n² ≥ cp*(H_n)/n² − 3·abs(e(H_n)/n² − k_n/n²)
                     → cp*(G)/N² − 3·abs(e(G)/N² − d) > a.

    The base graph is chosen first and n → ∞ afterwards.
- **Uniform convergence** (`Erdos1017.FractionalGraph.extremal_uniform_convergence`).
  For η > 0 there is N with abs(f*(n,k)/n² − F(k/n²)) < η for n ≥ N and all
  k ≤ C(n,2). Otherwise take n_i → ∞ with errors ≥ η and a subsequence with
  k_i/n_i² → d; along it f*/n² → F(d) by the same proof
  (`Erdos1017.FractionalGraph.tendsto_extremal_of_density_along`) and
  F(k_i/n_i²) → F(d) by continuity, a contradiction.

---

## 4. The lower bound F ≥ B

`Erdos1017/LowerBound/FiniteWeightedGraph.lean`, `Erdos1017/LowerBound/FractionalBipartite.lean`, `Erdos1017/LowerBound/FractionalCanonicalLimit.lean`, `Erdos1017/LowerBound/FractionalLimitEndpoints.lean`, `Erdos1017/LowerBound/IntegerBenchmarkLower.lean`, `Erdos1017/LowerBound/Repeat.lean`, `Erdos1017/LowerBound/WeightedGraphBenchmarkLower.lean`, `Erdos1017/LowerBound/WeightedGraphDual.lean`, `Erdos1017/LowerBound/WeightedGraphLeafDual.lean`, `Erdos1017/LowerBound/WeightedGraphLimit.lean`, `Erdos1017/LowerBound/WeightedGraphRealization.lean`, `Erdos1017/LowerBound/WeightedGraphSplitDual.lean`, `Erdos1017/LowerBound/WeightedGraphSplitLower.lean`, `Erdos1017/LowerBound/WeightedGraphTwoHeadDual.lean`, `Erdos1017/LowerBound/WeightedGraphTwoHeadLower.lean`.

Only weak duality is used; no optimality of the duals is claimed.

- **Weighted duals** (`Erdos1017.WeightedGraph.DualFeasible`,
  `Erdos1017.WeightedGraph.objective`). A dual on a base graph G is a
  symmetric charge y, zero off the edges, with Σ_{i<j in S} y_ij ≤ 1 on every
  clique S. For weights w, objective(w, y) = (1/2)Σ_{i,j} y_ij w_i w_j, and
  the weighted density is the same form with the adjacency matrix.
- **Weak duality** (`Erdos1017.WeightedGraph.realization`,
  `Erdos1017.WeightedGraph.realization_objective_le_densityLimit`,
  `Erdos1017.WeightedGraph.objective_le_densityLimit`). For a dual y and
  weights w ≥ 0 with Σw = 1, objective(w, y) ≤ F(density(G, w)). Let H
  replace vertex i by t_i independent copies, t = Σt_i. A clique of H maps
  injectively to a clique of G, so the pulled-back charge is a dual of H, and
  for a feasible weighting v of H, Σv_K ≥ Σv_K charge(K) = Σ_e y_e, whence
  cp*(H) ≥ (1/2)Σ y_ij t_i t_j. With w_i = t_i/t the candidate of H gives
  objective(w, y) ≤ cp*(H)/t² ≤ F(e(H)/t²) = F(density(G, w)). Real weights
  follow by rational approximation and continuity of F.
- **The integer inequality** (`Erdos1017.Repeat.discrete_quadratic_bound`).
  For natural t and j, t(2j + 1 − t) ≤ j(j + 1), since the difference is
  (t − j)(t − j − 1), a product of consecutive integers.
- **Split dual** (`Erdos1017.WeightedGraph.split_charge_le_one`,
  `Erdos1017.WeightedGraph.split_limit_lower`). On a complete base with one
  vertex P (weight a) and N tail vertices (weight u/N each):

      y(P, tail) = 2/(j + 1),   y(tail, tail′) = −2/(j(j + 1)).

  A clique with P and t tail vertices has charge t(2j + 1 − t)/(j(j + 1)) ≤ 1;
  without P it is ≤ 0. As N → ∞ (F is continuous), for a + u = 1,
  2au/(j + 1) − u²/(j(j + 1)) ≤ F((1 − a²)/2). With a = √(1 − 2d) the left
  side is the split polynomial of index j, so splitValue(√(1 − 2d)) ≤ F(d)
  (`Erdos1017.WeightedGraph.split_curve_le_densityLimit`).
- **E₂ dual** (`Erdos1017.WeightedGraph.complete_twoHead_charge_le_one`,
  `Erdos1017.WeightedGraph.complete_twoHead_limit_lower`). Complete base with
  parts P₁, P₂ (weights a, b) and a tail:

      y(P₁, P₂) = 1,  y(P₁, tail) = 2/3,  y(P₂, tail) = −2/3,  y(tail, tail′) = −1/3.

  With t tail vertices the charge is 1 − t(t − 1)/6 (with P₁ and P₂),
  t(5 − t)/6 ≤ 1 (P₁ only; the integer inequality with j = 2), or ≤ 0. In the
  limit, for a + b + u = 1, ab + (2/3)(a − b)u − u²/6 ≤ F((1 − a² − b²)/2).
- **W dual** (`Erdos1017.WeightedGraph.leaf_charge_le_one`,
  `Erdos1017.WeightedGraph.leaf_limit_lower`). A part P₀ (weight a) is joined
  only to a part P (weight b), and P to a complete tail:
  y(P₀, P) = 1, y(P, tail) = 2/(j + 1), y(tail, tail′) = −2/(j(j + 1)). A
  clique through P₀ lies in {P₀, P}; the others pass the split test. In the
  limit, ab + 2bu/(j + 1) − u²/(j(j + 1)) ≤ F(ab + bu + u²/2).
- **The branches** (`Erdos1017.WeightedGraph.mixed_parameter_lower`,
  `Erdos1017.WeightedGraph.twoHead_parameter_lower`). The W dual with j = 2
  and (a, b, u) = (1 + 3s − 3s², 4s + 1, s(4s + 1))/(s² + 8s + 2) has value
  mixedValue(s) at density 1/2 − mixedDensity(s) for s ∈ [σ_D, σ₀] (a ≥ 0
  since 3σ₀² − 3σ₀ − 1 = 0). For ε ∈ [1/8, 1/4], the W dual with j = 1,
  b = 1/2, u = √(1/2 − 2ε) and a = 1/2 − u has value ε at density 1/2 − ε
  (`Erdos1017.WeightedGraph.linear_mixed_lower`). The E₂ dual with
  (a, b, u) = (z(5z − 3)/4, z(1 − z)/4, (3z − 2)/2)/(z² + z − 1) has value
  twoHeadValue(z) at density 1/2 − twoHeadDensity(z) for z ∈ [2/3, z_C].
- **Endpoints** (`Erdos1017.FractionalGraph.densityLimit_eq_self`,
  `Erdos1017.FractionalGraph.densityLimit_half`). F(d) = d on
  [0, 1/4]: a subgraph of K_{t,t} with k_t = ⌊d(2t)²⌋ edges is bipartite, so
  its cliques are edges and f*(2t, k_t) = k_t; apply §3 along n = 2t. F(1/2) = 0:
  f*(n, C(n,2)) ≤ 1 since K_n is one clique.
- **Theorem** (`Erdos1017.WeightedGraph.benchmark_le_densityLimit`).
  B ≤ F on [0, 1/2]: both are d below 1/4, each branch of W and E₂ is at
  most F by the family duals above, and B(1/2) = 0.
- **Integer lower bound** (`Erdos1017.fractional_extremal_le_f`,
  `Erdos1017.benchmark_uniform_integer_lower`). An extremal G has
  f*(n,k) = cp*(G) ≤ cp(G) ≤ f(n,k); with §3, for η > 0 and n large,
  f(n,k)/n² > F(k/n²) − η ≥ B(k/n²) − η for every k ≤ C(n,2).
- **A lemma for §7** (`Erdos1017.Repeat.four_double_tight_repeat`). For
  j ≥ 1 and d′ ≤ e′ some self penalty in [0, 2d′e′/(j(j + 1))] keeps the
  rooted charge of r copies of one part type, at most one of the other and
  any number of tail vertices at most 1 (the integer core of §7's repeat).

---

## 5. The same-graph integer transfer

`Erdos1017/IntegerTransfer/SameGraphIntegerTransfer.lean`, `Erdos1017/IntegerTransfer/IntegerBenchmarkTransfer.lean`, `Erdos1017/IntegerTransfer/FixedDensityCleaning.lean`, `Erdos1017/IntegerTransfer/EquitableEqualization.lean`, `Erdos1017/IntegerTransfer/IntegerSubgraphRepair.lean`, `Erdos1017/IntegerTransfer/LabelledFractionalTruncation.lean`, `Erdos1017/IntegerTransfer/CleanedValueRounding.lean`, `Erdos1017/IntegerTransfer/CleanedGraphRounding.lean`, `Erdos1017/IntegerTransfer/MultipartiteFractionalAllocation.lean`, `Erdos1017/IntegerTransfer/CoupledProfilePacking.lean`, `Erdos1017/IntegerTransfer/ProfilePackingCost.lean`, `Erdos1017/IntegerTransfer/EmbeddedCliquePacking.lean`, `Erdos1017/IntegerTransfer/CoupledCliqueMatching.lean`, `Erdos1017/IntegerTransfer/ThinnedGraph.lean`, `Erdos1017/IntegerTransfer/CategoricalThinning.lean`, `Erdos1017/IntegerTransfer/CenteredThinningBudget.lean`, `Erdos1017/IntegerTransfer/MultipartiteTypicalExtensions.lean`, `Erdos1017/IntegerTransfer/ThinnedGraphMatching.lean`, `Erdos1017/IntegerTransfer/TransversalCliqueEdges.lean`, `Erdos1017/IntegerTransfer/TransversalCliqueMatching.lean`, `Erdos1017/IntegerTransfer/Nibble/HypergraphNearPerfectMatching.lean`, `Erdos1017/IntegerTransfer/Nibble/HypergraphNearPerfectWithOrder.lean`, `Erdos1017/IntegerTransfer/Nibble/HypergraphNibbleRun.lean`, `Erdos1017/IntegerTransfer/Nibble/HypergraphNibbleNormalizedStep.lean`, `Erdos1017/IntegerTransfer/Nibble/HypergraphNibbleIteration.lean`, and 88 further modules under `Erdos1017/IntegerTransfer/`.

The inequality cp(G) ≤ cp*(G) + o(n²) is the case with unit costs (their
t = 2) of Theorem 1.10 of Balogh, He, Krueger, Nguyen and Wigal (*Clique covers and
decompositions of cliques of graphs*, Adv. Comb. 2026:9), which proves a
general form. The Lean development proves the case it needs. In this section
the number of parts of a partition is written t and the part size N.

- **Theorem** (`Erdos1017.exists_same_graph_integer_upper_transfer`). For
  every η > 0 there is n₀ > 0 such that every graph G on n ≥ n₀ vertices
  satisfies cp(G) ≤ cp*(G) + ηn². The graph is not changed.
- **Corollary** (`Erdos1017.exists_integer_extremal_upper_transfer`). For
  every η > 0 there is n₀ > 0 with f(n,k) ≤ f*(n,k) + ηn² for all n ≥ n₀
  and all k: every k-edge graph has cp(G) ≤ cp*(G) + ηn² ≤ f*(n,k) + ηn²,
  and `Erdos1017.f_le_iff_cliquePartitionNumber` turns this into a bound on
  f. `Erdos1017.finalUniformAsymptotic` uses it with η/3 (§1).
- **Quantifier order.** Uniformity over all graphs on n vertices rests on
  the order of choices, and every stage theorem has the same shape: the
  regularity threshold ϑ₀ is chosen from the target error alone, before the
  bound p on the number of parts (which the regularity lemma derives from
  the regularity parameter), and the part-size threshold is chosen last.
  For example `Erdos1017.MultipartiteAllocation.exists_cleaned_value_rounding_tolerance`
  has the form "∃ ϑ₀ ∀ p, C ∃ n₀ ∀ N ≥ n₀ ∀ graphs".
- **Error budget of the top theorem.** Let σ = min(η, 1), κ = σ/128 (the
  cleaning density) and κ₀ = κ/2. Take ϑ₀ from the rounding stage with
  error σ/4 and density floor κ₀; choose the regularity parameter
  ϑ = min((ϑ₀/2)², κ/2, 1/4), ξ = σ/16, an integer l > 4/ξ, the Szemerédi
  bound p for (ϑ, l), C > 1/κ₀, the part-size threshold N₀ for (p, C), and
  n ≥ l + pN₀ + 64p/σ.
  - Cleaning (`Erdos1017.RegularityCleaning.exists_fixed_density_cleaning`,
    built on Mathlib's Szemerédi regularity lemma and its bound
    `SzemerediRegularity.bound`): an equitable ϑ-regular partition with l ≤ t ≤ p parts, and the subgraph
    keeping only the edges in ϑ-regular pairs of density at least κ, which
    loses fewer than (2ϑ + 2κ + ξ/4)n² edges.
  - Equalization (`Erdos1017.RegularityCleaning.equalized_pair`,
    `Erdos1017.RegularityCleaning.equalized_edge_loss`): keep N = ⌊n/t⌋ ≥ N₀
    vertices in each part. The resulting graph H ≤ G has independent parts,
    each pair empty or √ϑ-regular with density at least κ − ϑ ≥ κ₀, and
    loses fewer than (2ϑ + 2κ + ξ/4)n² + tn ≤ σn²/16 edges.
  - Rounding (stages 2 to 4 below):
    cp(H) ≤ cp*(H) + (σ/4)(tN)² ≤ cp*(H) + σn²/4, since √ϑ < ϑ₀.
  - Repair (`Erdos1017.cliquePartitionNumber_le_value_of_subgraph_rounding`):
    if H ≤ G and cp(H) ≤ cp*(H) + E, then
    cp(G) ≤ cp*(G) + E + 4(e(G) − e(H)). Each lost edge is a clique of its
    own (+1 integrally), and cp*(H) ≤ cp*(G) + 3(e(G) − e(H)) by
    `Erdos1017.FractionalGraph.value_le_edit_cost` (§3). Hence
    cp(G) ≤ cp*(G) + σn²/4 + 4σn²/16 ≤ cp*(G) + ηn².
- **Stage 2: truncation** (`Erdos1017.MultipartiteAllocation.exists_uniform_bounded_labelled_partition`).
  For τ > 0 there is b ≥ 3 such that every graph on t parts of size N has
  weights on cliques with 2 to b vertices, with load exactly one on every
  edge and total at most cp* + τ(tN)². Each clique of size s > b is replaced
  by uniform weights on its b-subsets; every pair keeps its load, and the
  cost grows by a factor C(s,2)/C(b,2), so the total excess is at most
  e(G)/C(b,2).
- **Stage 3: allocation and thinning** (`Erdos1017.MultipartiteAllocation.typeMass_pair_balance`,
  `Erdos1017.TransversalThinning.thinned`). Group the weights by profile,
  the set K of parts that a clique meets; for parts i ≠ j the profile masses
  over K ∋ i, j sum to the number e(i, j) of edges between i and j. Each
  profile is split into C layers with Cκ₀ ≥ 1, and every edge between parts
  i and j is sent independently to the layer (K, c), K ∋ i, j, with
  probability mass(K)/(C·e(i, j)); these probabilities sum to one. Writing
  α_K = mass(K)/(CN²) ≤ κ₀, the probability is α_K divided by the density of
  the pair (i, j), so each layer is the graph between the parts of K thinned
  to the common density α_K on every pair. Profiles of size 2 and layers
  with α_K below a floor α₀ are not matched; their edges are paid one each.
- **Stage 4: matching** (`Erdos1017.MultipartiteAllocation.exists_coupled_profile_matchings`,
  `Erdos1017.TransversalClique.exists_coupled_clique_matchings`). In one
  allocation outcome of positive probability, every matched layer has
  edge-disjoint transversal cliques covering a (1 − ρ) share of its edges,
  and a score measuring the residual edges stays below one. For each clique
  type, `Erdos1017.TransversalClique.packing_of_role_control` turns control
  of base counts, atypical bases and squared degree errors into a packing;
  `exists_coupled_clique_matchings` obtains that control for all types at
  once, in one positive-weight categorical outcome, by second-moment
  estimates built on the counting lemma
  `Erdos1017.MultipartiteExtension.exists_extension_tolerance`. The matching is
  found in the clique hypergraph (`Erdos1017.TransversalClique.hypergraph`),
  whose vertices are the graph edges and whose hyperedges are the edge sets
  of transversal cliques; near-regular degrees, small codegrees and a small
  aggregate squared error give a near-perfect matching
  (`Erdos1017.TransversalClique.exists_matching_of_squared_error`).
- **Accounting** (`Erdos1017.TransversalClique.cliquePartitionNumber_le_embedded_matchings`,
  `Erdos1017.MultipartiteAllocation.cliquePartitionNumber_map_le_profile_cost`,
  `Erdos1017.MultipartiteAllocation.exists_cleaned_rounding_tolerance`).
  A matched clique on k vertices replaces C(k,2) single edges, so
  cp ≤ e − Σ_i |T_i|(C(k_i,2) − 1). This gives
  cp ≤ #(residual edges) + (1 + ρC(b,2))(1 + ρ)·Σ(matched mass)/C. With
  ρ = τ/(16(C(b,2) + 1)) the factor is at most 1 + τ/8, the residual edges
  number less than the mass of the profiles of size 2 plus τ(tN)²/4, and in
  total cp(H) ≤ Σw + τ(tN)². With truncation error τ/2 and rounding error
  τ/2 this is the rounding stage
  `Erdos1017.MultipartiteAllocation.exists_cleaned_value_rounding_tolerance`.
- **The nibble** (`Erdos1017.HypergraphNibble.near_perfect_matching_with_exceptions`,
  `Erdos1017.HypergraphNibble.near_perfect_matching_with_order`,
  `Erdos1017.HypergraphNibble.exists_scheduled_rounds`,
  `Erdos1017.HypergraphNibble.exists_normalized_round`,
  `Erdos1017.HypergraphNibble.matchingRounds_accounting`). The matching
  interface is a Pippenger-type theorem with an exceptional set: an
  r-uniform hypergraph on n vertices with maximum degree at most C·D,
  codegrees at most γD and degrees in (1 ± γ)D outside at most γn
  exceptional vertices (D ≥ D₀) has a matching of at least (1 − ζ)n/r
  edges. It is proved by T rounds of a random nibble of intensity θ. Each
  round keeps disjoint selected edges, discards a set of waste vertices of
  second order in θ, and keeps the degrees of the surviving non-exceptional
  vertices inside explicit envelopes, while the exceptional set grows by a
  controlled amount; after T rounds,
  r·#(matching) + #(active) + #(waste) = n exactly, and the active set and
  the waste are small. The version with an order threshold n ≥ N₀ is
  proved first. The threshold is then dropped: for small n and large D₀ the
  hypotheses cannot hold, since a non-exceptional vertex exists (γ < 1) and
  would have degree at least (1 − γ)D > 2^n.

---

## 6. Limit models, compactness and the selected optimum

`Erdos1017/Models/Capped/CappedModel.lean`, `Erdos1017/Models/Capped/CappedGrowingLimit.lean`, `Erdos1017/Models/Capped/CappedAttainment.lean`, `Erdos1017/Models/Capped/CappedSamplingApproximation.lean`, `Erdos1017/Models/Capped/CappedLowerComparison.lean`, `vendor/Graphon/Graphon/Compactness.lean`, `Erdos1017/Models/Kernel/GraphonFamilyCompactness.lean`, `Erdos1017/Models/Decorated/DecoratedCompactness.lean`, `Erdos1017/Models/Capped/CappedLimitValue.lean`, `Erdos1017/Models/Capped/CappedRegularKernel.lean`, `Erdos1017/Models/Kernel/PositiveSpectralSubspace.lean`, `Erdos1017/Models/Capped/CappedAveraging.lean`, `Erdos1017/Models/Selection/FullKernelSelection.lean`, `Erdos1017/Models/Selection/FullStationaryCompactness.lean`, `Erdos1017/Models/Kernel/KernelPositiveIndexStability.lean`, `Erdos1017/Models/Selection/GlobalExcessMaximum.lean`, `Erdos1017/Models/Selection/FullGlobalExcess.lean`, `Erdos1017/Models/Selection/FullStationarySelection.lean`, and 133 further modules under `Erdos1017/Models/` and `vendor/Graphon/`.

Unless stated otherwise the carrier (Ω, μ) is a compact metric space with
its Borel σ-algebra and an atomless probability measure; the selection
theorems also need L²(μ) separable. The final theorem uses [0, 1] with
Lebesgue measure (§1).

- **Models** (`Erdos1017.CappedModel.Model`). A model W on (Ω, μ) is a
  random-color kernel: to each pair (x, y) it assigns a probability law on
  the colors {absent} ∪ {present with charge y, y ∈ [−3, 1]}, symmetric for
  μ×μ-almost every pair; G(x, y) is the probability of presence and Y(x, y)
  the mean charge. Deterministic pairs (G, Y) are the special case of point
  laws; random colors are what limits of charged graphs produce.
- **Feasibility** (`Erdos1017.CappedModel.Feasible`,
  `Erdos1017.CappedModel.FullFeasible`). W is r-feasible if for every
  2 ≤ n ≤ r, for μⁿ-almost every (x_1, …, x_n) and almost surely for
  independently sampled colors of the C(n,2) pairs, an n-tuple whose pairs
  are all present has total charge at most 1. It is fully feasible if this
  holds for every r.
- **Density and objective** (`Erdos1017.CappedModel.density`,
  `Erdos1017.CappedModel.objective`). d = (1/2)∫∫G and c = (1/2)∫∫Y.
- **Averaging** (`Erdos1017.CappedModel.averaged`). Replacing each present
  charge by its conditional mean keeps G, Y, d and c and preserves
  feasibility (`Erdos1017.CappedModel.feasible_averaged`): given that all
  pairs of an n-tuple are present, the expected total charge is the sum of
  the conditional means.
- **The sandwich** (`Erdos1017.CappedModel.capValue`,
  `Erdos1017.CappedModel.objective_le_densityLimit_add_cap_error`,
  `Erdos1017.CappedModel.densityLimit_le_capValue`,
  `Erdos1017.CappedModel.fullFeasible_objective_le_densityLimit`). Let
  capValue(r, d) be the supremum of c over r-feasible models of density
  exactly d.
  - Sampling: every r-feasible model (r ≥ 2) has c ≤ F(d) + d/C(r,2).
    Sample n points and their colors; almost surely the sampled charges pass
    every clique test of order at most r. The sampled graph has a fractional
    clique partition by cliques of order at most r of cost at most
    cp* + e/C(r,2) (as in §5, stage 2), and weak duality against it uses
    only tested orders; the density penalty of F and concentration of the
    sampled density finish as n → ∞. Letting r → ∞, every fully feasible
    model on any probability space has c ≤ F(d).
  - Realization: F(d) ≤ capValue(r, d) for every r and d ∈ [0, 1/2]. An
    optimal dual of a finite graph with charges in [−3, 1]
    (`Erdos1017.FractionalGraph.exists_bounded_dual`, §3) is realized as a
    fully feasible model on the atomless carrier, and the density is then
    restored at a cost of at most 3 per unit of density.
  - Together, 0 ≤ capValue(r, d) − F(d) ≤ 1/(2(n + 1)) for r ≥ n + 2
    (`Erdos1017.CappedModel.capValue_error_bound`).
- **Compactness** (`Erdos1017.GraphonFamily.compact_countable`,
  `Erdos1017.DecoratedKernel.compact_moments`). Cameron Freer's library
  (`vendor/Graphon/Graphon/Compactness.lean`) formalizes the compactness
  theorem of Lovász and Szegedy (L. Lovász and B. Szegedy, Szemerédi's lemma
  for the analyst, Geom. Funct. Anal. 17 (2007), 252–270): on a standard
  Borel atomless probability space, every sequence of graphons has a
  subsequence converging in cut distance. The development adapts that proof,
  with the library's regularity, energy-increment and completeness lemmas,
  to countable families of graphons: every sequence of such families has one
  subsequence and one sequence of measure-preserving relabelings under which
  every coordinate converges in cut norm. A common frame is needed because
  countably many moment graphons must be aligned at once. From it,
  `compact_moments`: every sequence of random-color kernels has a
  subsequence and measure-preserving alignments under which the joint color
  laws converge weakly and every continuous [0, 1]-valued color moment
  converges in cut norm, all in one common frame.
- **Attainment** (`Erdos1017.CappedModel.exists_fixedMeasureMaximizer`,
  `Erdos1017.CappedModel.exists_fullFeasible_growing_limit`,
  `Erdos1017.CappedModel.exists_fullFeasible_at_density`). For each r the
  capped supremum is attained. Models feasible at orders r_k → ∞ have a
  subsequential limit that is fully feasible, with all sampled continuous
  clique tests, densities and objectives converging. Applied to capped
  maximizers at density d with r = n + 2 this gives a fully feasible model
  with density d and objective F(d).
- **Shifted kernel and index** (`Erdos1017.CappedModel.shiftedKernel`,
  `Erdos1017.KernelOperator.positiveSpectralSubspace`). For a multiplier m,
  M = Y − mG = Y + ℓG, the mean of the shifted color (charge − m·presence);
  its integral operator on L²(μ) is compact and symmetric. The positive
  index is the dimension of the span of its eigenspaces for positive
  eigenvalues.
- **Stationary kernels** (`Erdos1017.CappedModel.exists_selected_full_kernel`).
  If W is fully feasible with c = F(d) and 0 < d < 1/2, there are an equally
  good fully feasible V (same density and objective), m ∈ [−3, 1] and ν with:
  the shifted color of V is almost surely equal to M; 0 ≤ M ≤ 4;
  (1 − G)M = 0; ∫M(x, ·)dμ = ν = 2(c − md) for almost every x; positive
  index at most 2. Outline: reweighting the vertex law by 1 + sf (f bounded,
  ∫f = 0) at fixed density gives a Lagrange multiplier m with (Y − mG)1
  constant and ⟨Mf, f⟩ ≤ 0 on {⟨G1, f⟩ = 0}, of codimension one in the
  mean-zero functions, which bounds the index by 2 (by 1 for constant
  degree). Deletion and insertion edits of colors give M ≥ 0, M ≤ 4 and
  (1 − G)M = 0, and complementarity makes the shifted color deterministic.
- **The stationary class** (`Erdos1017.CappedModel.FullStationaryClass`,
  `Erdos1017.CappedModel.stationaryEnergy`). FullStationaryClass d c W m
  means: W is fully feasible with density d and objective c = F(d);
  m ∈ [−3, 1]; for almost every pair the shifted color is almost surely
  M(x, y); 0 ≤ M ≤ 4 and (1 − G)M = 0 almost everywhere;
  ∫M(x, ·)dμ = 2(c − md) for almost every x; the positive index is finite
  and at most 2. Nothing stronger (no sign of m, no exact index) is part of
  the class. The energy is J(W, m) = ∫∫M² ∈ [0, 16]. By
  `Erdos1017.CappedModel.fullStationaryClass_nonempty` the class at
  (d, F(d)) is nonempty for every d ∈ (0, 1/2).
- **Closedness** (`Erdos1017.CappedModel.exists_aligned_fullStationary_limit`,
  `Erdos1017.KernelOperator.positive_index_le_of_tendsto`,
  `Erdos1017.CappedModel.isCompact_fullStationaryValues`). A sequence
  (W_n, m_n) in the class has a subsequence, alignments and a limit (V, m₀)
  in the same class, with joint laws, clique tests, multipliers, shifted
  operators (in operator norm), shifted kernels (in L²) and energies
  converging. The index bound passes to the limit because an operator-norm
  limit of compact symmetric operators with positive index at most 2 has
  positive index at most 2. Hence the set of attainable pairs (m, J) is a
  closed subset of [−3, 1] × [0, 16], and compact.
- **Two-stage selection** (`Erdos1017.CappedModel.exists_fullStationary_selection`).
  A nonempty class contains (W, m) with m minimal (ℓ maximal) and, among
  members with that m, J maximal: minimize the first coordinate on the
  compact set of pairs, maximize the second on the compact fiber, and take a
  model attaining the pair.
- **Positive global maximum** (`Erdos1017.exists_positive_global_excess`,
  `Erdos1017.CappedModel.exists_full_positive_global_excess`). If
  B(d₀) < F(d₀) for some d₀ ∈ [0, 1/2], then F − B, continuous on the
  compact [0, 1/2] (§2, §3), has a maximizer d with positive value; d > 1/4
  because F = B = d below 1/4, and d < 1/2 because F(1/2) = B(1/2) = 0
  (§4). An averaged fully feasible model at d with objective F(d) then has
  excess at least that of every fully feasible model on Ω under every law,
  whose objective is at most F(density).
- **Top theorem** (`Erdos1017.CappedModel.exists_selected_full_positive_global_excess`).
  If B(d₀) < F(d₀) for some d₀ ∈ [0, 1/2], there are d ∈ (1/4, 1/2), W and
  m with:
  - FullStationaryClass d F(d) W m;
  - c − B(d) > 0, where c = objective(W);
  - objective(V) − B(density V) ≤ c − B(d) for every probability law μ′ on
    Ω and every fully feasible V on (Ω, μ′);
  - m ≤ m′ for every member (V, m′) of the class at (d, F(d));
  - J(V, m) ≤ J(W, m) for every member (V, m) with the same multiplier.

  Proof: select in the class at the maximizer d of the previous item; the
  selected model has the same density and objective as the averaged
  maximizer, so it inherits its positive excess and its global maximality.
- **What §6 does not claim.** ℓ > 0, index exactly 2, strict support and
  nonconstant degree are not part of this theorem; §8 proves them for the
  selected model, using §7.

---

## 7. Multipartite profiles lie below B

`Erdos1017/Multipartite/MultipartiteBenchmarkTheorem.lean`, `Erdos1017/Multipartite/Multipartite.lean`, `Erdos1017/Multipartite/Selector/SelectorValue.lean`, `Erdos1017/Multipartite/Selector/SelectorBoundary.lean`, `Erdos1017/Multipartite/Selector/SelectorLinearProgram.lean`, `Erdos1017/Multipartite/Selector/SelectorSigns.lean`, `Erdos1017/Multipartite/ClosedAnchoring.lean`, `Erdos1017/Multipartite/MultipartiteCollision.lean`, `Erdos1017/Multipartite/MultipartiteDust.lean`, `Erdos1017/Multipartite/MultipartiteCountableDual.lean`, `Erdos1017/Multipartite/MultipartiteProfiles.lean`, `Erdos1017/Multipartite/MultipartiteProfileValues.lean`, `Erdos1017/Multipartite/MultipartiteCountableValue.lean`, `Erdos1017/Multipartite/MultipartiteRelabeling.lean`, `Erdos1017/Multipartite/MultipartiteExcessSelection.lean`, `Erdos1017/Multipartite/MultipartiteBenchmarkApplication.lean`, `Erdos1017/Multipartite/MultipartiteTrivialBound.lean`, `Erdos1017/Multipartite/MultipartiteLowDensityComparison.lean`, `Erdos1017/Multipartite/TwoHead/TwoHeadFamilyUpper.lean`, `Erdos1017/Multipartite/MultipartiteDenseComparison.lean`, `Erdos1017/Multipartite/MultipartiteWindowComparison.lean`, `Erdos1017/Multipartite/MultipartiteSelectedExcess.lean`, `Erdos1017/Multipartite/MultipartiteExcessHeadCount.lean`, `Erdos1017/Multipartite/TwoHead/TwoHeadProfileBridge.lean`, `Erdos1017/Multipartite/Selector/VertexRepeat.lean`, and 101 further modules under `Erdos1017/Multipartite/`.

A profile is a complete multipartite graph with an anchor part of mass 1,
countably many further independent parts of masses p_i ∈ [0, 1], and a
clique ("dust") of mass s ≥ 0; its total mass is 1 + T with T = s + Σp_i. The
section proves that the dual value of a profile (defined below), normalized
to mass one, is at most B at its own density. §8 uses it in the index-one
comparison (`selected_model.md` §8.2): a stationary model of positive index
at most one is replaced by a countable multipartite model with the same
density and objective, so its objective is at most B(d).

- **Theorem** (`Erdos1017.MultipartiteCountableDual.normalized_value_le_benchmark`).
  Let p_i ∈ [0, 1] be summable with Σp_i² ≤ 1, and s ≥ 0. Then

      value(p, s)/(1 + s + Σp_i)² ≤ B(1/2 − (1 + Σp_i²)/(2(1 + s + Σp_i)²)).

  The argument of B is the edge density of the profile at total mass one:
  the missing pairs are those inside the anchor and inside the parts p_i.
  The sorted form is `Erdos1017.MultipartiteProfiles.normalizedValue_le_benchmark`.
- **Value levels.** The value is defined at the dual level.
  - Finite LP (`Erdos1017.Multipartite.PrimalFeasible`,
    `Erdos1017.Multipartite.value`, `Erdos1017.Multipartite.Dual`). For part
    masses a_i, a clique selects at most one vertex from each part; a
    primal is a weighting w_X ≥ 0 of selections X, zero on selections of
    fewer than two parts, with Σ_{X ∋ i,j} w_X = a_i a_j for i ≠ j, and
    value(a) is the least total weight. A dual is a symmetric charge β_ij
    with total charge at most 1 on every selection.
  - Selector value (`Erdos1017.Selector.value`,
    `Erdos1017.Multipartite.largest_part_anchoring`). U(p) is the least total
    weight on nonempty subsets of {1, …, m} with first moments p_i and pair
    moments p_i p_j. If a_0 > 0 is a largest part, value(a) =
    a_0² U(a_i/a_0): every clique may be routed through the anchor, whose
    pair loads are the first moments. This uses exact selector duality
    `Erdos1017.Selector.exists_signed_primal_dual`: on the closed cube there
    is an attained primal and a dual (α, β) of equal value with 0 ≤ α_i ≤ 1
    and β_ij ≤ 0. In the interior this is finite LP duality
    (`Erdos1017.SelectorLinearProgram.exists_primal_dual`) and a sign
    argument by identification and deletion
    (`Erdos1017.Selector.interior_optimal_signs`); coordinates equal to 0 or
    1 are removed and restored.
  - Bounded dual with dust (`Erdos1017.MultipartiteDust.value`,
    `Erdos1017.MultipartiteCountableDual.value`). Cliques are rooted at the
    anchor. The coefficients lie in [0, 1]: a linear charge for each part,
    penalties for pairs of parts, part-to-dust penalties, a linear dust
    coefficient and a dust-to-dust penalty. They must give rooted charge at
    most 1 to every Boolean selection of parts with every natural number of
    dust vertices, and value(p, s) is the maximum of the corresponding
    quadratic objective in (p, s); the countable version imposes all finite
    prefix tests.
  - Profiles (`Erdos1017.MultipartiteProfiles.space`,
    `Erdos1017.MultipartiteProfiles.limitValue`,
    `Erdos1017.MultipartiteProfiles.density`,
    `Erdos1017.MultipartiteCountableDual.value_eq_profile_limit`,
    `Erdos1017.MultipartiteProfiles.exists_sorted_representative`). The
    compact space of pairs (T, p) with p decreasing in [0, 1], partial sums
    of p at most T ≤ L and of p² at most 1; dust is T − Σp_i. The limit of
    the finite-part values is continuous on the space and equals the
    countable dual value; sorting and zero parts change nothing.
- **Density cases** (`Erdos1017.MultipartiteProfiles.normalizedValue_le_benchmark_of_oneHead_family_bound`).
  With d the density of the profile:
  - d ≤ 1/4 (`Erdos1017.MultipartiteProfiles.normalizedValue_le_benchmark_of_le_quarter`):
    the normalized value is at most the normalized edge mass d = B(d)
    (partition into edges).
  - 1/4 ≤ d ≤ 3/8: `Erdos1017.MultipartiteProfiles.limitValue_le_max_oneHead`
    bounds the value by the larger of the one-part comparator and a third
    of the edge mass, with both moments T and Q = Σp_i² fixed, and
    B(d) ≥ d/3 on this range (`Erdos1017.Benchmark.benchmark_ge_third_of_low`).
    Idea: take a value maximizer with greatest dust on the fiber of fixed
    (T, Q). If its value exceeds a third of the edge mass, its optimal dual
    has unit dust coefficients, and a one-point promotion with a repeat
    completion would strictly improve the value at the same moments; so it
    has at most one secondary part.
  - 3/8 ≤ d ≤ 153/338: the window argument below.
  - d ≥ 153/338 (`Erdos1017.MultipartiteProfiles.normalizedValue_le_benchmark_of_dense`):
    the collision bound value ≤ splitValue(a_0) + (1/2)Σ(secondary squares)
    at total mass one (`Erdos1017.Multipartite.value_le_split_add_collision`
    for finitely many parts, then dust by equal cells) and the scalar
    comparison `Erdos1017.DenseMultipartite.collision_bound_le_benchmark`.
    The threshold is (1 − (4/13)²)/2 = 153/338.
- **One secondary part** (`Erdos1017.MultipartiteProfiles.oneHeadValue_le_benchmark`,
  `Erdos1017.TwoHeadFamilyUpper.normalized_value_le_benchmark`). For
  x ∈ [0, 1] and s ≥ 0 with density in [1/4, 1/2], the profile with one
  secondary part x and dust s has normalized value at most B(d). Cases:
  x = 1 (value 1, normalized value equal to the missing density
  1/2 − d ≤ B(d)); x + s ≤ 1 (normalized value at most the missing
  density); s ≥ 1 (at most the split value, and splitValue ≤ B); otherwise
  an explicit count law. The comparator of the previous cases is
  `Erdos1017.MultipartiteProfiles.oneHeadValue`, with one part of mass √Q and
  dust T − √Q, which has the same density.
- **The window** (`Erdos1017.MultipartiteProfiles.normalizedValue_le_benchmark_on_comparison_window`).
  A counterexample with density in [3/8, 153/338] has T ≤ 13/(2√2) − 1, so
  it lies in a compact window. The endpoints are covered by the other
  cases, so there is an interior maximizer of the excess
  normalized value − B(density) with positive excess, and among such
  maximizers one with greatest dust: dust is upper semicontinuous on the
  space (`Erdos1017.MultipartiteProfiles.dust_upperSemicontinuousOn`), while
  the total mass of the parts is not continuous, since mass can escape into
  infinitely many small parts. That maximizer has second part zero
  (`Erdos1017.MultipartiteCountableDual.selected_excess_second_head_zero`),
  so its value is the one-part comparator and the previous item gives a
  contradiction.
- **Second part zero.** Suppose p_1 > 0 at the selected maximizer.
  - If d < 21/50: every optimal dual of the profile has its own slope
    multiplier λ (the profile analogue of ℓ, written ℓ in Lean) at least
    minus the right slope of B, which is above 1/2 by the guards of §2; then
    there are exactly two positive secondary parts and positive dust
    (`Erdos1017.MultipartiteCountableDual.head_count_le_two_at_excess_maximum`),
    and this configuration is impossible when λ > 1/2
    (`Erdos1017.TwoHeadProfileBridge.two_positive_heads_positive_dust_impossible`).
  - If 21/50 ≤ d < 153/338: the same slope bound, the dense guards of §2
    (`Erdos1017.Benchmark.benchmark_dense_head_count_guards`) and the bound
    of the anchor share by the square root of the missing density
    (`Erdos1017.MultipartiteCountableDual.anchor_le_sqrt_missing`) put the
    mass threshold for a positive secondary part strictly below the mass
    available, so a second positive part is impossible
    (`Erdos1017.MultipartiteCountableDual.dense_selected_excess_impossible`).
- **The repeat lemma** (`Erdos1017.VertexRepeat.vertex_has_repeat`). The two-part
  impossibility reduces to a finite problem with seven coefficients. At a
  strictly positive vertex of its polytope at least seven count tests are
  tight, tight counts are adjacent, and the extracted pattern admits a
  one-sided repeat extension of one of the two part types with self penalty
  between 0 and the cross penalty. The integer core is
  `Erdos1017.Repeat.four_double_tight_repeat` (§4). A repeat contradicts the
  strict pair bounds at an optimal vertex.

---

## 8. The structure of the selected model (in `selected_model.md`)

See `selected_model.md`. Interface theorems used by §9 and §10:

- **Strict gap** (`Erdos1017.CappedModel.FullStationaryClass.strict_gap_structure`):
  a class member with d ∈ (1/4, 1/2) and B(d) < c has ℓ > 0, ν > 0, positive
  index exactly 2, nonconstant degree, γ > 0, G = 1{M > 0} almost
  everywhere, and a mean-zero eigenfunction of M with a positive eigenvalue.
- **Smooth contacts** (`Erdos1017.CappedModel.full_stationary_multiplier_eq_benchmark_deriv`):
  for a fully feasible global maximizer of objective − B(density), if B has
  derivative β at d, the rows of M are constant and the degree is not, then
  m = β, that is ℓ = −B′(d).
- **Selected structure** (`Erdos1017.CappedModel.FullStationaryClass.exists_selected_high_low_structure`):
  for a class member with d ∈ (1/4, 1/2), B(d) < c, m minimal and J maximal,
  a structure S exists (whole-row atoms, clique dust, zero cut, classes
  HIGH, LOW, NEUTRAL).
- **Reverse recovery** (`Erdos1017.CappedModel.SelectedHighLowStructure.exists_reverseRecovery`):
  every such S of a class member with d ∈ (1/4, 1/2) and B(d) < c has a
  reverse recovery, with plateau, height and S_P.

---

## 9. Where a positive maximum can sit

`Erdos1017/ContactLocation/BenchmarkMixedSplitJunction.lean`, `Erdos1017/ContactLocation/BenchmarkSplitCellClassification.lean`, `Erdos1017/ContactLocation/BenchmarkSplitCurvature.lean`, `Erdos1017/ContactLocation/BenchmarkSplitSideExtensions.lean`, `Erdos1017/ContactLocation/FullCuspContact.lean`, `Erdos1017/ContactLocation/FullMixedSplitJunction.lean`, `Erdos1017/ContactLocation/FullOneSidedContact.lean`, `Erdos1017/ContactLocation/FullPositiveContactCurvature.lean`, `Erdos1017/ContactLocation/FullSplitContactExclusion.lean`, `Erdos1017/ContactLocation/FullSplitContactLocation.lean`, `Erdos1017/ContactLocation/QuadraticOneSidedContact.lean`, `Erdos1017/ContactLocation/SelectedRemainingContact.lean`.

Standing hypotheses: (Ω, μ) is a standard Borel, compact metric, atomless
probability space with L²(μ) separable; FullStationaryClass d c W m with
d ∈ (1/4, 1/2) and B(d) < c; and W is a global maximizer:
objective(V) − B(density V) ≤ c − B(d) for every fully feasible V on Ω under
every probability law. Write ⟨Kf, g⟩ = ∫∫K(x, y)f(y)g(x) dμ(y)dμ(x) and 1
for the constant function.

**The second-variation test.** Let f be bounded, ∫f dμ = 0, a = ⟨G1, f⟩,
and for small s let W_s be W under the law (1 + sf)μ
(`Erdos1017.CappedModel.reweight`). W_s is fully feasible (the clique tests
are almost-everywhere statements), and exactly

    density(W_s) = d + sa + (s²/2)⟨Gf, f⟩,   objective(W_s) = c + s⟨Y1, f⟩ + (s²/2)⟨Yf, f⟩

(`Erdos1017.CappedModel.density_reweight_smul`,
`Erdos1017.CappedModel.objective_reweight_smul`). By global maximality
φ(s) = objective(W_s) − B(density(W_s)) has a local maximum at 0
(`Erdos1017.CappedModel.full_benchmark_reweight_local_max`). The rows of M
are constant, so ⟨M1, f⟩ = ν∫f = 0, that is ⟨Y1, f⟩ = ma = −ℓa.

- **(T1) Bracket** (`Erdos1017.CappedModel.full_stationary_multiplier_mem_slope_interval`,
  `Erdos1017.CappedModel.FullStationaryClass.multiplier_mem_one_sided_slopes_of_strict_gap`).
  If B has one-sided derivatives b₋, b₊ at d and the degree ∫G(x, ·)dμ is
  not a.e. constant (true by §8), then b₋ ≤ m ≤ b₊, i.e. −b₊ ≤ ℓ ≤ −b₋. With
  f the centred degree, a > 0; for small s > 0, φ(s) − φ(0) = s(m − b₊)a +
  o(s) ≤ 0, and with −f, s(m − b₋)(−a) + o(s) ≤ 0.
- **(T2) Smooth contact** (`Erdos1017.CappedModel.full_stationary_multiplier_eq_benchmark_deriv`,
  `Erdos1017.CappedModel.full_stationary_benchmark_curvature`). If B′(d) = β
  and the degree is nonconstant, m = β. If B is moreover C² at d, then
  ⟨Mf, f⟩ ≤ B″(d)a² for every bounded mean-zero f. Proof: first order on
  both sides gives (m − β)a = 0 for all f; then the first-order terms cancel
  and φ(s) − φ(0) = (s²/2)(⟨Yf, f⟩ − β⟨Gf, f⟩ − B″(d)a²) + o(s²) =
  (s²/2)(⟨Mf, f⟩ − B″(d)a²) + o(s²) ≤ 0.
- **(T3) One side** (`Erdos1017.SmoothContact.quadratic_right_curvature`). Let
  β̃ be a function, C² at d, with β̃ = B on [d, d + θ) and m = β̃′(d). If
  a > 0 then ⟨Mf, f⟩ ≤ β̃″(d)a²; the mirror statement holds on (d − θ, d]
  with a < 0. Proof: for small s ≥ 0 the density stays where B = β̃, and the
  expansion of (T2) for s ≥ 0 suffices.
- **(P) A positive transverse direction.** By §8, M has a mean-zero
  eigenfunction w with eigenvalue σ > 0; w = σ⁻¹Mw is bounded and
  ⟨Mw, w⟩ = σ‖w‖² > 0 (`Erdos1017.CappedModel.exists_positive_direction_of_eigenvector`).
  Directions with a = 0 have ⟨Mf, f⟩ ≤ 0 by fixed-density optimality
  (c = F(d)) and a Lagrange multiplier, so a ≠ 0
  (`Erdos1017.CappedModel.full_positive_direction_transverse`); take a > 0.
- **Positive curvature** (`Erdos1017.CappedModel.FullStationaryClass.benchmark_second_deriv_pos_of_strict_gap`).
  If B is C² at d, then 0 < ⟨Mw, w⟩ ≤ B″(d)a², so B″(d) > 0.

The test is used three times: split cells, the W/split junction, and the
two ends of the cusp bracket.

- **Use 1, split geometry** (`Erdos1017.Benchmark.split_cell_or_reciprocal`,
  `Erdos1017.Benchmark.benchmark_second_deriv_neg_split_cell`). If
  1/2 − ε* < d < 1/2, B is the split curve (ε < ε* < ε_C) and
  r = √(1 − 2d) ∈ (0, 1/2) is 1/k with k ≥ 3 or lies in a strict cell
  1/(j + 1) < r < 1/j, j ≥ 2, where B is C²
  (`Erdos1017.Benchmark.benchmark_contDiffAt_split_cell`) and, as dr/dd = −1/r,

      B′(d) = (2(2j + 1) − 2(j + 1)/r)/(j(j + 1)),   B″(d) = −2/(j r³) < 0.

- **Theorem** (`Erdos1017.CappedModel.FullStationaryClass.no_split_cell_contact`,
  `Erdos1017.CappedModel.FullStationaryClass.split_contact_is_reciprocal`).
  No contact lies in a strict split cell, by positive curvature; so a
  contact with 1/2 − ε* < d < 1/2 has √(1 − 2d) = 1/k and
  d = (1 − 1/k²)/2 with k ≥ 3.
- **Use 2, junction slopes** (`Erdos1017.Benchmark.benchmark_mixed_split_left_hasDerivWithinAt`,
  `Erdos1017.Benchmark.benchmark_mixed_split_right_hasDerivWithinAt`). At d* = 1/2 − ε*, both one-sided derivatives of
  B are −(√21 − 1)/6. Right of d*, B is the index-2 split polynomial as a
  function of d (`Erdos1017.Benchmark.splitDensityExtension`), C² and
  strictly concave below 1/2 (`Erdos1017.Benchmark.splitDensityExtension_second_deriv_neg`),
  with slope 5/3 − 1/r = (1 − √21)/6 at r = (9 − √21)/10.
- **Theorem** (`Erdos1017.CappedModel.FullStationaryClass.no_mixed_split_junction_contact`).
  No contact at d*: (T1) gives m = −(√21 − 1)/6, the slope of the concave
  extension β̃, and (P) with (T3) gives 0 < ⟨Mf, f⟩ ≤ β̃″(d*)a² ≤ 0
  (`Erdos1017.CappedModel.FullStationaryClass.multiplier_ne_right_concave_slope_of_strict_gap`).
- **Use 3, cusp slopes** (`Erdos1017.Benchmark.split_cusp_left_hasDerivAt`,
  `Erdos1017.Benchmark.split_cusp_right_hasDerivAt`). At d_k = (1 − 1/k²)/2, k ≥ 3, B is the
  split polynomial of index k − 1 on the left, of slope −U_k, and of index k
  on the right, of slope −L_k (substitute r = 1/k in B′).
- **Theorem** (`Erdos1017.CappedModel.FullStationaryClass.split_cusp_strict_slope`,
  in `Erdos1017/Exclusions/Cusp/FullSplitCuspContact.lean`, used in §10.5). At a cusp contact
  L_k < ℓ < U_k < 2: (T1) gives the closed bracket, and (T3) with f on the
  concave right extension and −f on the concave left one excludes the ends
  (`Erdos1017.CappedModel.FullStationaryClass.multiplier_ne_left_concave_slope_of_strict_gap`).
- **Assembly: definition** (`Erdos1017.CappedModel.RemainingBenchmarkContact`).
  RemainingBenchmarkContact d m holds if, with ε = 1/2 − d:
  - (E₂) some q ∈ (0, 213/1000) has ε ∈ (ε_C, 1/4), W(ε) < E₂(ε),
    d = (1 − h(q))/2, B(d) = twoHeadValue((q + 2)/3), B′(d) = −ℓ(q) and
    m = −ℓ(q); or
  - (corner) ε ∈ (ε_C, ε_D) and E₂(ε) = W(ε); or
  - (cusp) some k ≥ 3 has √(1 − 2d) = 1/k and d = (1 − 1/k²)/2.
- **Theorem** (`Erdos1017.CappedModel.SelectedHighLowStructure.remaining_benchmark_contact`).
  Under the standing hypotheses and for a selected structure S,
  RemainingBenchmarkContact d m holds. If ε < ε*, Use 1 gives a cusp; ε = ε*
  is excluded by Use 2; if ε > ε*, `Erdos1017.Benchmark.family_contact_alternatives`
  leaves three cases. Strict W is excluded by
  `Erdos1017.CappedModel.SelectedHighLowStructure.no_smoothW_contact`, the
  case analysis of §10.1 on S (no curvature argument: B″ has no useful sign
  on the W branch). Strict E₂ gives q by
  `Erdos1017.Benchmark.strict_twoHead_contact_parameters` and m = −ℓ(q) by
  (T2). Equality is the corner.
- **Theorem** (`Erdos1017.CappedModel.exists_selected_remaining_contact`). If
  B(d₀) < F(d₀) for some d₀ ∈ [0, 1/2], there are d ∈ (1/4, 1/2), W, m with
  FullStationaryClass d F(d) W m, B(d) < F(d), global maximality, a selected
  structure S and RemainingBenchmarkContact d m: §6
  (`Erdos1017.CappedModel.exists_selected_full_positive_global_excess`) gives
  d, W, m with positive excess, minimal m and maximal J; §8 gives S; the
  previous theorem gives the contact.

---

## 10. The exclusions (in `exclusions.md`)

See `exclusions.md`. Each theorem assumes a selected structure S of a class
member at (d, c), B(d) < c and global maximality, and proves False from:

- **Smooth W** (`Erdos1017.CappedModel.SelectedHighLowStructure.no_smoothW_contact`):
  d ∈ (1/4, 1/2), ε ∈ (ε*, ε_D), E₂(ε) < W(ε); used inside §9.
- **Lower E₂** (`Erdos1017.CappedModel.SelectedHighLowStructure.no_lowerE2_contact`):
  q ∈ (0, 1/10], d = (1 − h(q))/2.
- **Middle E₂** (`Erdos1017.CappedModel.SelectedHighLowStructure.no_middle_e2_contact_of_cover`):
  the cover premise, q ∈ (1/10, 1/5), d = (1 − h(q))/2,
  B(d) = twoHeadValue((q + 2)/3), B′(d) = −ℓ(q).
- **Upper E₂** (`Erdos1017.CappedModel.SelectedHighLowStructure.no_upperE2_contact`):
  q ∈ [1/5, 213/1000] and the same data.
- **Cusps** (`Erdos1017.CappedModel.SelectedHighLowStructure.no_cusp_contact`):
  k ≥ 3, d = (1 − 1/k²)/2.
- **Corner** (`Erdos1017.CappedModel.SelectedHighLowStructure.no_corner_global_excess`):
  d ∈ (1/4, 1/2), ε ∈ [ε_C, ε_D], E₂(ε) = W(ε).

---

## 11. Certificates (in `certificates.md`)

See `certificates.md`.

- **Cover** (`Erdos1017.MiddleE2LargeUniversal.FixedPoint.cover_root`):
  cover 80 IBox.root = true, a depth-bounded dyadic bisection of a box in
  (q, A, b, u) whose leaves pass a fixed-point interval test, each by
  `decide +kernel`.
- **Soundness** (`Erdos1017.MiddleE2LargeUniversal.FixedPoint.priceTests_of_cover`):
  given the cover, every real point with 157/1000 ≤ q ≤ 1/5,
  1/3 ≤ A ≤ 369/1000, 0 ≤ b, u ≤ 1/3 satisfying the necessary inequalities of
  middle E₂ passes the strict price tests; the proof never evaluates the
  cover or a leaf test, and §10.4 uses it once.
- **Other certificates.** Bernstein positivity certificates for the corner
  (§11.3, used in §10.6) and closed-form scalar inequalities (§11.4, used in
  §2, §6, §7 and §10). Only the 148 generated pieces of the cover use
  `decide +kernel`.
