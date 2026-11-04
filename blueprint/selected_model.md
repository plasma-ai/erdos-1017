# Blueprint: the structure of the selected optimal model

This document holds §8 of the blueprint (sections 8.0 to 8.11); `proof.md`
holds the statement, §0 to §7 and §9. Like the rest of the blueprint it
gives its part of the argument in prose, following the Lean development
module by module and naming the modules and declarations of each section,
with the conventions, notation and credits of `proof.md`. It starts from the
selected model of §6 and ends with the reverse recovery that every exclusion
of §10 (`exclusions.md`) uses.

Input from `proof.md` §6 and §7: `Erdos1017.CappedModel.FullStationaryClass`,
`Erdos1017.CappedModel.exists_selected_full_positive_global_excess`,
`Erdos1017.MultipartiteCountableDual.normalized_value_le_benchmark`.

---

## 8.0 Setting and scope

`Erdos1017/Models/Selection/FullStationaryCompactness.lean`,
`Erdos1017/Models/Selection/FullStationarySelection.lean` (inputs from §6); the 205
modules of §8 are those of `Erdos1017/SelectedModel/` and its subfolders.

**Notation.** G, Y, M also denote their integral operators on L²(μ);
⟨·,·⟩ is the inner product, 1 the constant function and g = G1 the degree
(always the degree of G, never of M). A *direction* is a bounded f with
∫f dμ = 0, and Q_M(f) = ⟨Mf, f⟩ is its shifted energy.

**The model.** Fix d, c, W, m with W in `Erdos1017.CappedModel.FullStationaryClass`
d c W m (`proof.md` §6): W is fully feasible with density d and objective
c = F(d); m ∈ [−3, 1]; for μ×μ-almost every pair the sampled shifted color
is almost surely M(x,y); M ∈ [0, 4] and (1 − G)M = 0 almost everywhere;
∫M(x,y) dμ(y) = ν for μ-almost every x; and the positive spectral subspace of
M has dimension at most two. If B(d₀) < F(d₀) for some d₀ ∈ [0, 1/2],
then on a compact metric carrier with atomless μ and L²(μ) separable,
`Erdos1017.CappedModel.exists_selected_full_positive_global_excess` supplies
such a model with 1/4 < d < 1/2 and c − B(d) > 0, and with:

- (hglobal) objective(V) − B(density(V)) ≤ c − B(d) for every probability
  measure μ′ on the measurable space Ω and every fully feasible V on (Ω, μ′);
- (hmin) m ≤ m′ for every class member on (Ω, μ) at (d, c) with multiplier
  m′, that is, ℓ is maximal;
- (hmax) ∫∫M_V² ≤ ∫∫M² for every class member V with the same m
  (`Erdos1017.CappedModel.stationaryEnergy`).

**Carrier and scope.** From 8.2 on, theorems assume Ω standard Borel with
measurable diagonal, every singleton μ-null (μ atomless) and L²(μ)
separable; the selection of §6 and the results of 8.4 also need Ω compact
metric with its Borel σ-algebra. The final theorem uses Ω = [0, 1] with
Lebesgue measure. Every structural theorem assumes c > B(d), and uses the
size of B only through 8.2, B(d) ≥ 1/2 − d, and B(d) = d for d ≤ 1/4 (8.4).
Saturation (8.10) assumes in addition ℓ < 1; the bounds |P| ≤ 2 on the
plateau (8.9) assume ℓ ≥ 2/3, or ℓ > 1/2 with ε > 1/12. The facts ℓ > 0,
γ > 0 and the stabilizing clique order are conclusions, not hypotheses.

---

## 8.1 First variation and smooth contacts

`Erdos1017/SelectedModel/Selection/FullSmoothContact.lean`.

**The variational idea.** For a direction f and |s|·‖f‖∞ < 1, W read under
the probability law (1 + s f)μ is a model W_s. It is fully feasible, since
feasibility is an almost-sure statement about sampled tuples and survives an
absolutely continuous change of the vertex law. Exactly,

    density(W_s)   = d + s⟨G1, f⟩ + (s²/2)⟨Gf, f⟩,
    objective(W_s) = c + s⟨Y1, f⟩ + (s²/2)⟨Yf, f⟩.

If the rows of M are constant, M1 = ν1 gives ⟨Y1, f⟩ = −ℓ⟨G1, f⟩, hence

    objective(W_s) + ℓ·density(W_s) = c + ℓd + (s²/2) Q_M(f).

Most competitors below are reweightings of this kind, possibly after an
edit that leaves M unchanged, and their comparison with F reduces to the
sign of Q_M. To keep the density at d, it is corrected exactly along a
direction χ with ⟨G1, χ⟩ ≠ 0 and Q_M(χ) > 0 (8.3), and the competitor is
compared with F(d) = c.

- **Reweighted local maximum**
  (`Erdos1017.CappedModel.full_benchmark_reweight_local_max`). If W is fully
  feasible and satisfies (hglobal), then for every direction f the function
  s ↦ c + s⟨Y1, f⟩ + (s²/2)⟨Yf, f⟩ − B(d + s⟨G1, f⟩ + (s²/2)⟨Gf, f⟩) has a
  local maximum at s = 0: each W_s competes in (hglobal).
- **Multiplier at a smooth contact**
  (`Erdos1017.CappedModel.full_stationary_multiplier_eq_benchmark_deriv`).
  Let W be fully feasible with (hglobal), B differentiable at d with
  derivative β, ∫M(x,y) dμ(y) constant in x almost everywhere, and the degree
  g not almost everywhere constant. Then m = β, that is, ℓ = −B′(d).
  - The first variation gives ⟨Y1, f⟩ = β⟨G1, f⟩ for every direction;
    constant rows give ⟨Y1, f⟩ = m⟨G1, f⟩; some direction has ⟨G1, f⟩ ≠ 0.
- **Curvature test**
  (`Erdos1017.CappedModel.full_stationary_benchmark_curvature`). Under the
  same hypotheses, with B twice continuously differentiable at d, every
  bounded f ∈ L²(μ) with ∫f dμ = 0 satisfies

      Q_M(f) ≤ B″(d)·⟨G1, f⟩².

  - The second variation is ⟨Yf, f⟩ − B′(d)⟨Gf, f⟩ − B″(d)⟨G1, f⟩² ≤ 0,
    and B′(d) = m. No tangency ⟨G1, f⟩ = 0 is required.

Both apply to the selected model (its degree is not constant, 8.3); they
serve `proof.md` §9 and `exclusions.md`, not the rest of this file.

---

## 8.2 The index-one comparison

`Erdos1017/SelectedModel/Selection/FullIndexOneComparison.lean`,
`Erdos1017/SelectedModel/ZeroClass/CountableZeroClassReplacement.lean`,
`Erdos1017/SelectedModel/MultipartiteValue/FiniteMultipartiteBenchmark.lean`.

- **Index-one comparison**
  (`Erdos1017.CappedModel.full_objective_le_benchmark_of_index_one`). On the
  carrier of 8.0, let W be fully feasible, m ∈ [−3, 1], ν > 0,
  ∫M(x,y) dμ(y) = ν for μ-almost every x, M ≥ 0 and (1 − G)M = 0
  μ×μ-almost everywhere, the shifted color deterministic, and the positive
  spectral subspace of M of dimension at most one. Then
  objective(W) ≤ B(density(W)). No optimality is assumed.
  - Features (`Erdos1017.CappedModel.exists_index_one_active_classes`).
    1 is an eigenvector for ν > 0, so index at most one makes M − ν(1 ⊗ 1)
    negative semidefinite: M(x,y) = ν − ⟨Φ(x), Φ(y)⟩ almost everywhere for a
    measurable Φ into ℓ² with ‖Φ‖ ≤ √ν. By Cauchy–Schwarz, M(x,y) = 0
    exactly when ‖Φ(x)‖ = √ν and Φ(x) = Φ(y), so the zero set of M is the
    union of the squares of the boundary classes {Φ = v}, ‖v‖ = √ν. The
    *active* classes, those of positive measure on which G is not almost
    everywhere 1, are countably many; each carries with positive
    probability a sampled clique of some order n and has internal density
    at most 1 − 1/n. Outside their squares G = 1 almost everywhere.
  - Replacement
    (`Erdos1017.CappedModel.objective_le_benchmark_of_active_boundary_data`).
    On the atomless carrier every active class is replaced by a complete
    n-partite patch with the same internal adjacency mass
    (`Erdos1017.CappedModel.exists_atomless_zeroClass_patch_of_density_bound`),
    all at once. This gives a fully feasible V on (Ω, μ) with the density
    and objective of W whose adjacency is almost surely 1 exactly between
    different labels (one label per part, singletons elsewhere).
  - Comparison with §7
    (`Erdos1017.CappedModel.objective_le_benchmark_of_partition_support`).
    Almost every finite sample of V is a complete multipartite graph whose
    sampled charges are a feasible dual for its fractional clique
    partition. Weak duality and the finite form of §7 bound the sampled
    charge by B of the sampled density, and the samples concentrate.
- **Finite multipartite benchmark**
  (`Erdos1017.Multipartite.value_le_benchmark`). For finitely many masses
  a_i ≥ 0 with Σ a_i = 1, the fractional clique partition value of the
  complete multipartite profile with part masses a_i is at most
  B((1 − Σ a_i²)/2); it is derived from
  `Erdos1017.MultipartiteCountableDual.normalized_value_le_benchmark`
  (`proof.md` §7).

Hence a class member with c > B(d) has index exactly two (8.3); the proved
bound "profile values ≤ B" is used, never a multipartite envelope.

---

## 8.3 The strict-gap structure

`Erdos1017/SelectedModel/Selection/FullStrictGapStructure.lean`.

- **Strict-gap structure** (`Erdos1017.CappedModel.FullStrictGapStructure`).
  For W, m and ν, the record of: (i) m < 0, that is ℓ > 0; (ii) ν > 0; (iii)
  the positive spectral subspace of M has dimension exactly two; (iv) the
  degree is not almost everywhere constant, equivalently f ↦ ⟨G1, f⟩ is
  not zero on directions; (v) γ = ν + m = ν − ℓ > 0; (vi) strict support:
  μ×μ-almost everywhere, G = 1 where M > 0 and G = 0 where M ≤ 0; (vii)
  some w ≠ 0 in L²(μ) with ∫w dμ = 0 has Mw = σw for some σ > 0.
- **Every class member above B has it**
  (`Erdos1017.CappedModel.FullStationaryClass.strict_gap_structure`). On the
  carrier of 8.0, if W is in the class at (d, c, m), 1/4 < d < 1/2 and
  B(d) < c, the structure holds with ν = 2(c + ℓd). No selection is used.
  - c > 1/2 − d, because B(d) ≥ 1/2 − d on [1/4, 1/2]
    (`Erdos1017.Benchmark.benchmark_ge_missing`).
  - ℓ > 0 (`Erdos1017.CappedModel.full_multiplier_neg_of_complement_excess`):
    for m ≥ 0, Y = M + mG ≥ 0, and a fully feasible model with nonnegative
    charge has c + d ≤ 1/2
    (`Erdos1017.CappedModel.full_moment_nonnegative_objective_add_density_le_half`).
    Then ν = 2c + 2ℓd > 0.
  - Index two: index at most one gives c ≤ B(d) by 8.2.
  - Nonconstant degree
    (`Erdos1017.CappedModel.full_regular_of_strict_benchmark_gap`): with
    constant degree, the averaged model (charges replaced by conditional
    means; same density, objective and adjacency) carries, by the singular
    branch of the kernel selection of §6, a stationary nonnegative shifted
    kernel of index at most one, and 8.2 gives c ≤ B(d).
  - Eigenvector (`Erdos1017.CappedModel.exists_positive_meanzero_eigenvector`):
    a second positive eigenvector is orthogonal to the eigenvector 1.
  - Tangent inequality
    (`Erdos1017.CappedModel.full_regular_tangent_nonpositive`): every
    direction f with ⟨G1, f⟩ = 0 has Q_M(f) ≤ 0. Density-preserving
    reweightings cannot beat F(d) = c; the Lagrange condition has a
    multiplier, equal to m because the degree is not constant. So the
    bounded direction χ built from w, with Q_M(χ) > 0, has ⟨G1, χ⟩ ≠ 0.
  - γ > 0 (`Erdos1017.CappedModel.full_gamma_pos_of_positive_eigenvector`):
    make a fraction τ of the mass universal and restore the density exactly
    along s·χ. Optimality gives Q_M(χ)s² ≤ 2γ(τ + τ²/2) with s of order τ,
    which rules out γ ≤ 0.
  - Strict support
    (`Erdos1017.CappedModel.full_strict_support_of_positive_eigenvector`):
    deleting, with probability θ, the present pairs with M = 0 leaves M
    unchanged and keeps full feasibility. If these pairs had positive
    measure, restoring the density along χ would gain Q_M(χ)s²/2 > 0 over
    F(d). With (1 − G)M = 0 this gives G = 1[M > 0].

---

## 8.4 Finite-order stabilization and the physical primal

`Erdos1017/SelectedModel/Capped/CappedFiniteOrderStabilization.lean`,
`Erdos1017/SelectedModel/Capped/CappedPhysicalPrimal.lean`,
`Erdos1017/SelectedModel/Selection/FullStrictGapPhysicalPrimal.lean`.

For K ≥ 2, F_K(d) = `Erdos1017.CappedModel.capValue` Ω μ K d is the supremum
of objective(V) over models V on (Ω, μ) of density d that are feasible for
clique orders at most K; F_K(d) ≥ F(d) for d ∈ [0, 1/2].

- **Stabilization**
  (`Erdos1017.CappedModel.exists_finite_order_equality_of_strict_gap`). Let Ω
  be compact metric and standard Borel, μ atomless, L²(μ) separable. If
  0 ≤ d < 1/2 and B(d) < F(d), some N₀ ≥ 2 has F_{N₀}(d) = F(d).
  - d > 1/4 is derived, since F(d) = B(d) = d for d ≤ 1/4.
  - Each cap K has a maximizer at density d whose averaged form carries a
    stationary shifted kernel. By compactness, for all large K every such
    record has m < 0, nonconstant degree, γ ≥ γ₀ and every positive
    eigenvalue at least s₀, with γ₀, s₀ > 0 independent of K
    (`Erdos1017.CappedModel.exists_uniform_cap_gap_bounds`).
  - Finite arity
    (`Erdos1017.CappedModel.fullFeasible_of_explicit_spectral_budget`): with
    these gaps, strict support and index at most two, almost every clique of
    the strict-support graph whose order exceeds an explicit budget in γ₀
    and s₀ has negative total charge. So beyond the budget a K-feasible
    maximizer is fully feasible, its objective is at most F(d), and
    F_K(d) = F(d).
- **Physical representative**
  (`Erdos1017.CappedModel.PhysicalRepresentative.adjacency`,
  `Erdos1017.CappedModel.PhysicalRepresentative.charge`). G_ph(x,y) = 1 if
  and only if M(x,y) > 0 and M(y,x) > 0; Y_ph = (Y(x,y) + Y(y,x))/2 on G_ph
  and 0 off it. "Physical" means realized by points of Ω: unlike the
  kernels, these are defined and symmetric at every pair, so "a clique of
  G_ph" is a pointwise notion. Under strict support,
  G_ph = G and Y_ph = Y μ×μ-almost everywhere
  (`Erdos1017.CappedModel.PhysicalRepresentative.adjacency_moment_ae_eq`,
  `Erdos1017.CappedModel.PhysicalRepresentative.charge_ae_eq`).
- **Physical primal**
  (`Erdos1017.CappedModel.exists_original_physical_primal_of_finite_order_equality`).
  Let Ω be compact metric with countably generated Borel σ-algebra and μ
  atomless, and let W be fully feasible with objective(W) = F(d), strict
  support, deterministic shifted color, and F_{N₀}(d) = F(d) for some
  N₀ ≥ 2. Then there are finite measures ζ_n on Ωⁿ, zero unless
  2 ≤ n ≤ N₀, invariant under permutation of coordinates, such that
  - ζ_n-almost every tuple is injective and a clique of {G = 1};
  - the ordered pair occupation Σ_n Σ_{i≠j} (x_i, x_j)_* ζ_n is the measure
    G(x,y) μ(dx) μ(dy) (in unordered terms, the pair demand G·μ²/2);
  - Σ_n ζ_n(Ωⁿ) = c, and ζ_n-almost every tuple is tight:
    (1/2)Σ_{i≠j} Y(x_i, x_j) = 1.

  Bounded-order cliques thus form an optimal fractional clique partition of
  the limit object, each tight for the dual Y.
- **Packaged form**
  (`Erdos1017.CappedModel.FullStationaryClass.exists_physical_primal_of_strict_gap`).
  On a compact metric, standard Borel, atomless carrier with L²(μ)
  separable, a class member with d < 1/2 and B(d) < c has such N₀ and ζ_n
  of cost c (strict support by 8.3).
  - The primal averages optimal N₀-capped fractional partitions of finite
    samples of (G_ph, Y_ph), passes to a weak limit with complementary
    slackness and returns to the moment kernels
    (`Erdos1017.CappedModel.physical_graphDemand_eq_momentDemand`).
    Distinct-point sampling needs the atomless carrier: on a one-point space
    a positive diagonal demand has no injective cliques.

---

## 8.5 Selection and null rigidity

`Erdos1017/SelectedModel/Selection/SelectedStrictGapModel.lean`,
`Erdos1017/SelectedModel/Selection/FullSelectedNullRigidity.lean`.

The selected model of 8.0 has c > B(d), so 8.3 applies to it; χ denotes the
transverse direction of 8.3. The first selection, (hmin), adds rigidity.

- **Null rigidity**
  (`Erdos1017.CappedModel.FullStationaryClass.selected_tangent_null_vector_rigidity_of_strict_gap`).
  On the carrier of 8.0, let W be in the class, 1/4 < d < 1/2, B(d) < c,
  with (hmin). If f ∈ L²(μ) is bounded, ∫f dμ = 0, ⟨G1, f⟩ = 0 and
  Q_M(f) = 0, then ⟨Gf, f⟩ = 0 and Mf = 0 in L²(μ), that is,
  ∫M(x,y)f(y) dμ(y) = 0 for μ-almost every x.
  - Zero adjacency energy (`Erdos1017.CappedModel.full_tangent_null_density`,
    which uses no selection). Reweight by 1 + s f + τ χ with τ = τ(s)
    chosen so that the density is d:
    (s²/2)⟨Gf, f⟩ + τ(⟨G1, χ⟩ + s⟨Gf, χ⟩) + (τ²/2)⟨Gχ, χ⟩ = 0. By 8.1 the
    competitor's gain over c is sτ⟨Mf, χ⟩ + (τ²/2)Q_M(χ), which must be
    ≤ 0. If ⟨Gf, f⟩ ≠ 0, τ has exact order s², and the cubic term (for the
    right sign of s) or the positive quartic term violates this.
  - Null row
    (`Erdos1017.CappedModel.FullStationaryClass.selected_null_row_of_adjacency_null`).
    Now W_s (law (1 + s f)μ) has density d and, by 8.1, objective c, so it
    is optimal; for small s it lies in the stationary class on its own law
    (`Erdos1017.CappedModel.FullStationaryClass.eventually_reweight`), and
    pairing its row identity with χ shows that its multiplier m(s) is a
    linear-fractional function of s with m(0) = m. Transported back to
    (Ω, μ) it competes in (hmin), so m(s) ≥ m near 0; a linear-fractional
    function with a local minimum is constant, and then M(1 + s f) = ν1 = M1
    gives sMf = 0.

Every result of this part concerns the one selected model W: the two
selections and the global comparison stay attached to it. Their assembly
with the contact location is
`Erdos1017.CappedModel.exists_selected_remaining_contact` (`proof.md` §9).

---

## 8.6 Whole-row atoms, clique dust and the zero cut

`Erdos1017/SelectedModel/FullDiffuseCompletion.lean`,
`Erdos1017/SelectedModel/Structure/SelectedZeroBipartition.lean`,
`Erdos1017/SelectedModel/Structure/SelectedWholeRowStructure.lean`.

The *row map* is a strongly measurable ρ: Ω → L²(μ) with ρ(x) = M(x, ·) for
μ-almost every x. Its fibers {ρ = r} are measurable, and those of positive
measure are disjoint, hence countably many.

- **Diffuse completion**
  (`Erdos1017.CappedModel.FullStationaryClass.ae_complete_diffuse_of_two_clique_cover`).
  On the carrier of 8.0, let W be in the class, 1/4 < d < 1/2, B(d) < c. If
  a measurable D′ is covered up to a null set by measurable C₀, C₁ with
  G_ph = 1 at μ×μ-almost every pair inside each C_b, then G = 1
  μ×μ-almost everywhere on D′ × D′.
  - Give the missing pairs of D′ × D′ the charge −ℓ, leaving M unchanged.
    Moving clique counts along zero pairs (a convex step) shows that every
    finite clique of the completed graph has charge at most 1, so partial
    random completions are fully feasible. Completing with probability θ
    and restoring the density along χ gives objective c + s(θ)²Q_M(χ)/2,
    with s(θ) of order θ times the missing mass: above F(d) = c unless that
    mass is zero.
- **Index-two features**
  (`Erdos1017.KernelOperator.exists_uniform_feature_of_stationary_positive_index_two`;
  no selection). Constant rows ν > 0, 0 ≤ M ≤ 4, index at most two and a
  mean-zero eigenvector with eigenvalue at least s₀ > 0 give a feature map
  Φ into ℓ², with ‖Φ‖ ≤ √(8 + 32/s₀) almost everywhere, and a self-adjoint
  isometry J such that M(x,y) = ⟨JΦ(x), Φ(y)⟩ μ×μ-almost everywhere. This
  representation serves the diffuse completion above, the finite-arity
  theorem of 8.4 and the flow energy of 8.8.
- **Canonical geometry**
  (`Erdos1017.CappedModel.FullStationaryClass.exists_canonical_middle_exclusion`).
  There are σ > 0, a normalized ψ (∫ψ = 0, ∫ψ² = 1, Mψ = σψ) and a feature
  map Ψ into ℓ² with M(x,y) = ν + σψ(x)ψ(y) − ⟨Ψ(x), Ψ(y)⟩
  μ×μ-almost everywhere, and a conull set on which, at every pair, the right
  side is ≥ 0 and ‖Ψ(x)‖² ≤ ν + σψ(x)². Using (hmax), on that set
  ρ(x) = ρ(z) exactly when (ψ, Ψ) agree, and for μ-almost every y its zero
  neighbours on one side of ψ(y) form a null set. Idea: ordered zero triples
  close (triangle inequality on the sphere); an isotropic affine plane of
  positive measure carries at most two row values
  (`Erdos1017.CappedModel.FullStationaryClass.isotropic_plane_two_rowMap_values_of_strict_gap`),
  or a direction supported on it would raise ∫∫M² at fixed m; and the
  countably many positive-measure rows exclude vertices with zero
  neighbours on both sides.
- **Zero cut**
  (`Erdos1017.CappedModel.FullStationaryClass.exists_zero_relation_bipartition`,
  uses (hmax)). Some measurable T ⊆ Ω is crossed by μ×μ-almost every pair
  with M(x,y) = 0 and ρ(x) ≠ ρ(y).
- **Whole-row structure**
  (`Erdos1017.CappedModel.FullStationaryClass.exists_whole_row_structure`,
  uses (hmax)). There are ρ, a countable set I of row values, a set D and a
  measurable T such that:
  - for r ∈ I the *atom* I_r = {ρ = r} is measurable, μ(I_r) > 0, G = 0
    almost everywhere on I_r × I_r, and its rows are homogeneous
    (`Erdos1017.KernelOperator.WholeRowFiberData`): almost every x ∈ I_r has
    M(x, ·) = r, G(x, ·) = 1[r > 0] and Y(x, ·) = r − ℓ·1[r > 0];
  - the atoms are disjoint and D = Ω ∖ ∪_{r∈I} I_r is measurable;
  - G = 1 μ×μ-almost everywhere on D × D (D is the *clique dust*);
  - T is a zero cut, and each fiber of positive measure lies almost
    everywhere inside T or almost everywhere outside T.

  A fiber of positive measure is internally independent or complete; the
  atoms are the independent ones. Inside one side of the cut, zero pairs
  have identical rows and so lie, up to a null set, in independent fibers;
  hence D meets each side in a clique of G_ph
  (`Erdos1017.CappedModel.FullStationaryClass.exists_independent_rows_two_clique_sides`),
  and diffuse completion makes D complete.

For r ∈ I, its *outside missing region* Z_r is the set of x ∉ I_r with
r(x) = 0: the points not joined to the atom
(`Erdos1017.KernelOperator.wholeFiberMissingSet`).

---

## 8.7 The HIGH, LOW and NEUTRAL classes

`Erdos1017/SelectedModel/Structure/SelectedHighLowClassification.lean`.

- **Outside missing pairs** (`Erdos1017.CappedModel.actualZeroRelation`).
  Z = {(x,y) : M(x,y) = 0 and ρ(x) ≠ ρ(y)}, a measurable set of pairs
  defined pointwise. By strict support, up to a null set, these are the
  non-adjacent pairs not inside one row fiber.
- **The classes** (`Erdos1017.OrderedZeroRelation.highClass` and its
  companions). For a fixed measurable version of g:
  H = {x : μ{y : (y,x) ∈ Z, g(y) < g(x)} > 0} (HIGH),
  L = {x : μ{y : (x,y) ∈ Z, g(y) > g(x)} > 0} ∖ H (LOW),
  N = Ω ∖ (H ∪ L) (NEUTRAL): a partition of Ω at every point.
- **The selected structure**
  (`Erdos1017.CappedModel.SelectedHighLowStructure`). A structure S for W
  and m consists of ρ, I, D, T with all the properties of 8.6, the classes
  H, L, N of Z and g, and:
  - μ×μ-almost every pair of Z has g(x) ≠ g(y);
  - for μ-almost every x, μ{y : (y,x) ∈ Z, g(y) < g(x)} = 0 or
    μ{y : (x,y) ∈ Z, g(y) > g(x)} = 0;
  - μ×μ-almost every pair of Z joins H to L, with larger degree at the HIGH
    end;
  - for μ-almost every x ∈ N, μ{y : (x,y) ∈ Z} = 0;
  - every atom lies almost everywhere in one class (the atom is HIGH, LOW
    or NEUTRAL);
  - μ×μ-almost every pair with M = 0 lies inside one atom or in Z.
- **Existence**
  (`Erdos1017.CappedModel.FullStationaryClass.exists_selected_high_low_structure`).
  On the carrier of 8.0, if W is in the class, 1/4 < d < 1/2, B(d) < c, and
  (hmin) and (hmax) hold, a structure S exists.
  - 8.6 gives ρ, I, D, T. Since the dust is complete, almost every pair of
    Z has an endpoint in an atom.
  - Degrees
    (`Erdos1017.CappedModel.FullStationaryClass.ae_actual_zero_relation_degree_ne`,
    `Erdos1017.CappedModel.FullStationaryClass.ae_actual_zero_relation_no_both`).
    For each atom, the degrees on Z_r lie all strictly below or all strictly
    above the atom's degree
    (`Erdos1017.CappedModel.FullStationaryClass.whole_atom_missing_degree_one_side`),
    and almost no dust point misses two atoms whose degrees straddle its own
    (`Erdos1017.CappedModel.FullStationaryClass.ae_diffuse_no_degree_straddle`).
    The atom fact uses (hmin), through the null rigidity of 8.5; the dust
    fact uses only the class and the cut.
  - The crossing of H and L and the null sections of N then follow
    abstractly (`Erdos1017.OrderedZeroRelation.ae_relation_crosses_high_low`);
    atoms lie in one class because their rows are homogeneous.

NEUTRAL atoms have no outside missing neighbours: G = 1 almost everywhere
between a NEUTRAL atom and the complement of its fiber
(`Erdos1017.CappedModel.SelectedHighLowStructure.neutral_atom_adjacency`);
`exclusions.md` calls them universal.

**Quantities.** The *atom mass* a_r = μ(I_r)
(`Erdos1017.CappedModel.SelectedHighLowStructure.originalAtomMass`, in
`Erdos1017/Exclusions/Common/SelectedDiffuseIncidence.lean`); the *outside section
mass* μ{y : (y,x) ∈ Z} of a point x
(`Erdos1017.CappedModel.SelectedHighLowStructure.outsideSectionMass`, in
`Erdos1017/SelectedModel/Structure/WholeRowMissingMass.lean`); the *body energy*
∫_{(Ω∖U)²} max(Y, 0)² d(μ×μ) of a measurable U ⊆ Ω
(`Erdos1017.PhysicalPrimal.bodyPositiveEnergy`, in
`Erdos1017/Exclusions/Common/Physical/PhysicalPositiveCover.lean`), zero exactly when
Y ≤ 0 almost everywhere on (Ω ∖ U)².

---

## 8.8 Missing flows and the forward peak

`Erdos1017/SelectedModel/Flows/FullForwardFlowClass.lean`,
`Erdos1017/SelectedModel/Flows/FullForwardPeak.lean`,
`Erdos1017/SelectedModel/Flows/OriginalForwardPeakLargest.lean`.

From here on S is a structure of 8.7 for the selected W, and theorems
assume the class, 1/4 < d < 1/2, B(d) < c and the carrier. No selection
hypothesis is used from here on: every result holds for any structure S of
any class member above B.

- **Flows**
  (`Erdos1017.CappedModel.SelectedHighLowStructure.IsFullForwardFlow`,
  `Erdos1017.CappedModel.SelectedHighLowStructure.IsFullReverseFlow`). A
  forward flow is an integrable φ ≥ 0 supported almost everywhere on
  Z ∩ (H × L) whose second marginal φ₂(y) = ∫φ(x,y) dμ(x) is 1_L almost
  everywhere. With φ₁(x) = ∫φ(x,y) dμ(y) and v_φ = φ₁ − φ₂, the *endpoint*
  W_φ is W under μ_φ = (1 + v_φ)μ: fully feasible, with every LOW point's
  mass moved to its HIGH partners. A reverse flow is the mirror image (on
  Z ∩ (L × H), second marginal 1_H, endpoint on L ∪ N). Write
  E(φ) = ∫∫M(x,y)v_φ(x)v_φ(y) dμ dμ, and a_r(φ) = μ_φ(I_r) for the endpoint
  masses (`Erdos1017.CappedModel.SelectedHighLowStructure.forwardClassMass`).
- **Endpoint budget**
  (`Erdos1017.CappedModel.SelectedHighLowStructure.IsFullForwardFlow.endpoint_budget`,
  `Erdos1017.CappedModel.SelectedHighLowStructure.IsFullReverseFlow.endpoint_budget`;
  class membership suffices). For every forward or reverse flow,

      γ + E(φ) = 2·objective(W_φ) − ℓ(1 − 2·density(W_φ)).

  The right side is ∫∫M(1 + v)(1 + v) − ℓ = ν + 2⟨M1, v⟩ + E(φ) − ℓ with
  v = v_φ, and ⟨M1, v⟩ = ν∫v = 0.
- **Endpoint shape.** E(φ) ≥ 0
  (`Erdos1017.CappedModel.FullStationaryClass.missing_flow_energy_nonnegative`,
  `Erdos1017.CappedModel.FullStationaryClass.reverse_missing_flow_energy_nonnegative`,
  via the index-two features of 8.6, the tangent inequality of 8.3,
  conditional feature barycentres and product densities). Almost every zero
  pair of M lies in an atom or in Z ⊆ (H × L) ∪ (L × H), so the endpoint is
  complete multipartite (a part per atom, singletons on the dust); hence
  1 − 2·density(W_φ) = Σ_r a_r(φ)², and objective(W_φ) ≤ (max_r a_r(φ))²
  (`Erdos1017.MultipartiteClassMasses.objective_le_class_bound_sq`, the
  model form of the §7 largest-part bound). Forward endpoints have density
  above d, reverse ones below d
  (`Erdos1017.CappedModel.SelectedHighLowStructure.IsFullForwardFlow.endpoint_density_gt`,
  `Erdos1017.CappedModel.SelectedHighLowStructure.IsFullReverseFlow.endpoint_density_lt`).
- **Peak gap** (`Erdos1017.CappedModel.forwardPeakGap`). Δ = γ if ℓ ≥ 1,
  Δ = 2c − h if ℓ < 1; both are positive (8.3 and c > 1/2 − d).
- **Common forward peak**
  (`Erdos1017.CappedModel.SelectedHighLowStructure.exists_unique_common_forward_peak`).
  Δ > 0, and exactly one atom i is a *common forward peak*
  (`Erdos1017.CappedModel.SelectedHighLowStructure.IsCommonForwardPeak`):
  every forward flow φ has a_i(φ) > 0, a_i(φ) = max_r a_r(φ) and
  a_r(φ) + Δ ≤ a_i(φ) for all r ≠ i.
  - One flow. Let a_max = max_r a_r(φ), let a′ be another endpoint mass,
    and h_φ = Σ a_r(φ)² ≥ a_max² + a′². The budget, E ≥ 0 and the
    largest-part bound give γ ≤ 2a_max² − ℓh_φ (so a_max > 0); also
    h_φ < h, and a_max + a′ ≤ 1 gives a_max² − a′² ≤ a_max − a′. If ℓ ≥ 1,
    γ ≤ 2a_max² − h_φ ≤ a_max − a′. If ℓ < 1, write
    γ = (1 − ℓ)h + (2c − h); then
    2c − h ≤ 2a_max² − ℓh_φ − (1 − ℓ)h < 2a_max² − h_φ ≤ a_max − a′.
  - All flows. Flows form a convex set with affine endpoint masses
    (`Erdos1017.CappedModel.SelectedHighLowStructure.IsFullForwardFlow.classMass_affine`);
    on a segment, Δ-separated peaks at parameters closer than Δ coincide, so
    the peak is constant (`Erdos1017.ForwardPeak.exists_common_separated_peak`).
  - Remark (not used later). For ℓ ≥ 2 the same bound would give
    γ ≤ 2a_max² − 2h_φ ≤ 0, so in fact 0 < ℓ < 2.
- **The peak is the largest atom**
  (`Erdos1017.CappedModel.SelectedHighLowStructure.exists_unique_largest_original_forward_peak`).
  Δ > 0, and the peak i has mass A = a_i > 0, is HIGH or NEUTRAL, and
  satisfies: a_r + μ(Z_r) ≤ A − Δ for every HIGH atom r ≠ i;
  sup_{r≠i} a_r < A; and for b₀ ∈ (0, A], if the HIGH dust points x with
  μ{y : (y,x) ∈ Z} > b₀ have positive measure, then

      γ ≤ (2 − ℓ)A² − ℓb₀².

  - Most of this comes from
    `Erdos1017.CappedModel.SelectedHighLowStructure.exists_controlled_diffuse_peak_atom`
    (in `Erdos1017/Exclusions/Common/ControlledDiffuseAtomization.lean`): the peak and
    its class (LOW atoms have endpoint mass 0), the bounds for HIGH and
    NEUTRAL atoms, and the displayed inequality. A flow avoiding the peak as
    recipient
    (`Erdos1017.CappedModel.SelectedHighLowStructure.exists_fullForwardFlow_avoiding_atom`)
    leaves it with mass A. For the inequality, a flow is built in which a
    set of HIGH dust points carries endpoint mass b₀ (this uses the outside
    sections above b₀); treating that set as one more part of the endpoint
    (atomization) in the largest-part bound and the budget gives it. LOW
    atoms below A come from
    `Erdos1017.CappedModel.SelectedHighLowStructure.low_atom_mass_lt_controlled_peak`.

---

## 8.9 Reverse plateau bounds

`Erdos1017/SelectedModel/Recovery/FullReversePlateau.lean`.

For a reverse flow φ, a_r(φ) = μ_φ(I_r)
(`Erdos1017.CappedModel.SelectedHighLowStructure.reverseClassMass`); HIGH
atoms have endpoint mass 0.

- **Plateau budget**
  (`Erdos1017.CappedModel.SelectedHighLowStructure.IsFullReverseFlow.plateau_budget`).
  If a_r(φ) ≤ t for every atom and a_r(φ) = t on a finite set P of atoms,

      γ + E(φ) ≤ 2t² − ℓ(1 − 2·density(W_φ)) ≤ (2 − ℓ|P|)t².

  Use objective(W_φ) ≤ t² and |P|t² ≤ Σ_r a_r(φ)² = 1 − 2·density(W_φ).
- **Consequences**, for t > 0, from γ > 0 and E(φ) ≥ 0:
  - |P| < 2/ℓ
    (`Erdos1017.CappedModel.SelectedHighLowStructure.IsFullReverseFlow.plateau_card_lt_two_div_neg_multiplier`);
  - |P| ≤ 2 if ℓ ≥ 2/3
    (`Erdos1017.CappedModel.SelectedHighLowStructure.IsFullReverseFlow.plateau_card_le_two_of_neg_multiplier_ge_two_thirds`);
  - |P| ≤ 2 if ℓ > 1/2 and ε > 1/12
    (`Erdos1017.CappedModel.SelectedHighLowStructure.IsFullReverseFlow.plateau_card_le_two_of_half_lt_neg_multiplier`):
    if ℓ < 2/3 and |P| ≥ 3, then |P|·t ≤ Σ_r a_r(φ) ≤ 1
    (`Erdos1017.CappedModel.SelectedHighLowStructure.IsFullReverseFlow.plateau_mass_bounds`)
    gives t ≤ 1/3, so γ ≤ (2 − 3ℓ)t² < 1/18, while
    c > ε gives γ = 2c − 2ℓε > 2ε(1 − ℓ) > 1/18;
  - endpoint credit
    (`Erdos1017.CappedModel.SelectedHighLowStructure.IsFullReverseFlow.endpoint_credit`):
    density(W_φ) < d and c + E(φ)/2 + ℓ(d − density(W_φ)) ≤ t², so c < t².

---

## 8.10 Saturation, the square reserve and body energy

`Erdos1017/SelectedModel/Saturation/SelectedSaturatedPairEnergy.lean`,
`Erdos1017/SelectedModel/Saturation/SelectedSaturationAtomic.lean`,
`Erdos1017/SelectedModel/Saturation/SelectedSaturatedPairCapacity.lean`,
`Erdos1017/SelectedModel/Saturation/SelectedSaturatedPairUniqueness.lean`,
`Erdos1017/SelectedModel/OriginalAtomicSquareReserve.lean`,
`Erdos1017/SelectedModel/SelectedBodyEnergy.lean`. Atom mass, outside section mass
and body energy are defined at the end of 8.7.

- **Saturated pair**
  (`Erdos1017.CappedModel.SelectedHighLowStructure.IsSaturatedAtomPair`).
  Atoms r ≠ u with Y = 1 μ×μ-almost everywhere on I_r × I_u.
- **Saturation lives between atoms**
  (`Erdos1017.CappedModel.SelectedHighLowStructure.ae_saturated_pair_between_distinct_original_atoms`).
  If ℓ < 1, μ×μ-almost every pair with Y = 1 joins two distinct atoms.
  Sampling large cliques in the complete dust gives Y ≤ ℓ on D × D
  (`Erdos1017.CappedModel.SelectedHighLowStructure.charge_le_neg_multiplier_on_diffuse_sq`)
  and Y ≤ (1 + ℓ)/2 on I_r × D
  (`Erdos1017.CappedModel.SelectedHighLowStructure.charge_le_half_one_sub_multiplier_on_atom_diffuse`),
  almost everywhere; G = 0 inside atoms.
- **Existence**
  (`Erdos1017.CappedModel.SelectedHighLowStructure.exists_saturated_atom_pair_of_positive_mass`).
  If ℓ < 1 and μ×μ{Y = 1} > 0, a saturated pair exists (almost every pair
  with Y = 1 lies in a saturated block I_r × I_u).
- **Uniqueness**
  (`Erdos1017.CappedModel.SelectedHighLowStructure.IsSaturatedAtomPair.unique`).
  If ℓ < 1, two saturated pairs coincide as unordered pairs. Pairs sharing
  an atom coincide
  (`Erdos1017.CappedModel.SelectedHighLowStructure.IsSaturatedAtomPair.eq_or_disjoint`,
  through `Erdos1017.CappedModel.SelectedHighLowStructure.IsSaturatedAtomPair.other_head_eq`);
  for disjoint pairs, the directions 1_{I_r}/a_r + 1_{I_u}/a_u − 2 have a
  degree-tangent combination with Q_M > 0, against the tangent inequality.
  So {Y = 1} is I_r × I_u ∪ I_u × I_r up to a null set
  (`Erdos1017.CappedModel.SelectedHighLowStructure.IsSaturatedAtomPair.ae_charge_one_iff_between_heads`).
- **Square reserve**
  (`Erdos1017.CappedModel.SelectedHighLowStructure.exists_original_atomic_square_reserve`;
  no condition on ℓ). Δ > 0, and the common forward peak i of 8.8 (HIGH or
  NEUTRAL, mass A > a_r for r ≠ i) satisfies, with sums over all atoms,

      γ + ℓ Σ_r a_r² ≤ 2A²   and   Σ_{r≠i} a_r² < A².

  - In a flow avoiding i every endpoint mass is at most A. From such a flow,
    by choosing receivers, redirecting finitely often and atomizing, every
    finite family F of LOW atoms satisfies
    γ + ℓ(Σ_{r not LOW} a_r² + Σ_{r∈F} a_r²) ≤ 2A²
    (`Erdos1017.CappedModel.SelectedHighLowStructure.IsFullForwardFlow.finite_low_square_reserve`);
    exhausting the LOW atoms gives the first inequality.
  - Write Σ₂ = Σ_r a_r². If ℓ ≤ 1, then Σ₂ ≤ h
    (`Erdos1017.CappedModel.SelectedHighLowStructure.originalAtomMass_sq_sum_le_missing_density`)
    and γ = (1 − ℓ)h + (2c − h), so Σ₂ ≤ (1 − ℓ)h + ℓΣ₂ < γ + ℓΣ₂ ≤ 2A²;
    if ℓ > 1, Σ₂ ≤ ℓΣ₂ < γ + ℓΣ₂ ≤ 2A². Subtract A².
- **Body energy**
  (`Erdos1017.CappedModel.FullStationaryClass.bodyPositiveEnergy_eq_physicalBody`).
  For a class member with 1/4 < d < 1/2, B(d) < c and measurable U, the body
  energy of U equals the same integral for Y_ph (8.4), by strict support.

---

## 8.11 Reverse recovery

`Erdos1017/SelectedModel/Recovery/SelectedReverseAssignment.lean`,
`Erdos1017/SelectedModel/Recovery/SelectedReverseRecovery.lean`.

An atom is *eligible* if it is LOW or NEUTRAL
(`Erdos1017.CappedModel.SelectedHighLowStructure.eligibleReverseAtom`). The
eligible missing atoms of a HIGH point x are the eligible r with x ∈ Z_r,
and its diffuse supply is κ(x) = μ{y ∈ D ∩ L : (y,x) ∈ Z}.

- **Assignment data**
  (`Erdos1017.CappedModel.SelectedHighLowStructure.ReverseAssignmentData`).
  A coding of the atoms by ℕ, masses a_i (of the eligible atom coded i, else
  0), allowed sets (Z_r for the eligible atom r coded i, else empty), κ, and
  a feasible start read off the normalized reverse flow. An assignment
  (λ_i) on (H, μ) is feasible if 0 ≤ λ_i ≤ 1, λ_i = 0 off the allowed set
  of i, finite partial sums are at most 1, and Σ_{i∈J} λ_i = 1 almost
  everywhere on {κ = 0, allowed codes = J} for each finite J. Code i has
  mass a_i + ∫_H λ_i dμ.
- **Compulsory source**
  (`Erdos1017.CappedModel.SelectedHighLowStructure.reverseCompulsorySource`).
  For a finite set P of atoms, S_P is the set of HIGH x with κ(x) = 0 that
  have eligible missing atoms, all of them in P.
- **Reverse recovery**
  (`Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery`). Data,
  a feasible λ, a height t > 0 and a nonempty finite plateau P of codes
  with: every mass at most t, with equality exactly on P; for almost every
  HIGH source, Σ_i λ_i = 1 if κ = 0 and all λ_i = 0 if κ ≠ 0; the completed
  flow (atomic fractions plus the normalized diffuse relation where κ > 0)
  a reverse flow;
  Σ_{i∈P} λ_i = 1_{S_P} almost everywhere on H; and
  |P|·t = Σ_{i∈P} a_i + μ(S_P). Decoded on atoms, the plateau
  (`Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.plateau`)
  consists of eligible atoms
  (`Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.plateau_eligible`),
  the reverse endpoint masses are at most t
  (`Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.classMass_le`)
  with equality exactly on it
  (`Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.classMass_eq_iff`),
  and |P|·t = Σ_{r∈P} a_r + μ(S_P)
  (`Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.original_source_balance`);
  for P = {p} with a_p = b, t = b + μ(S_P).
- **Existence**
  (`Erdos1017.CappedModel.SelectedHighLowStructure.exists_reverseRecovery`).
  Under the hypotheses of 8.8, every S has a reverse recovery.
  - Data come from the normalized reverse flow
    (`Erdos1017.CappedModel.SelectedHighLowStructure.exists_reverseAssignmentData`);
    a reverse endpoint has density below 1/2, so some eligible atom has
    positive mass.
  - Completion
    (`Erdos1017.ReverseAssignment.exists_completed_atomic_assignment`).
    Minimize Σ_i (a_i + ∫λ_i)² over feasible λ (weakly compact; the
    objective is lower semicontinuous). At a minimizer no source with κ > 0
    feeds an atom, and no source feeds an atom of larger final mass while
    allowed a smaller one; so the top level set P is finite and fed exactly
    by S_P, which gives the balance. Residual mass of sources with
    infinitely many allowed atoms is routed below t.
  - The completed flow is a reverse flow
    (`Erdos1017.CappedModel.SelectedHighLowStructure.ReverseAssignmentData.completedFlow_isFullReverseFlow`).
- **Plateau bounds of the recovery.** 8.9 applies to the recovered flow:
  |P| < 2/ℓ
  (`Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.card_lt_two_div_neg_multiplier`);
  |P| ≤ 2 if ℓ ≥ 2/3, or if ℓ > 1/2 and ε > 1/12
  (`Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.card_le_two_of_neg_multiplier_ge_two_thirds`,
  `Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.card_le_two_of_half_lt_neg_multiplier`);
  and c < t² (`Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.endpoint_credit`).
