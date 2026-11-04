# Blueprint: excluding every contact

This document holds §10 of the blueprint (sections 10.0 to 10.6); `proof.md`
holds the statement, §0 to §7 and §9. Like the rest of the blueprint it
gives its part of the argument in prose, following the Lean development
module by module and naming the modules and declarations of each section,
with the conventions, notation and credits of `proof.md`. Each exclusion is
a case tree on one selected model; every leaf is named, one leaf per range
is proved in full and the others are summarized with their Lean names.
Lean's multiplier m is always written −ℓ here, and k is the cusp index of
§10.5.

Input from `selected_model.md`: the selected structure S, the forward peak
and square reserve, saturation, body energy and the reverse recovery.
Input from `proof.md` §9: the contact type and its parameters. Input from
`certificates.md`: the certified scalar facts, cited by name only.

**Where the exclusions are used.** `proof.md` §9 shows that a selected
model at a positive global maximum of F − B lies at a remaining contact
(`Erdos1017.CappedModel.RemainingBenchmarkContact`): an E₂ point with
q ∈ (0, 213/1000), the W/E₂ corner, or a reciprocal cusp. Split cells and
the W/split junction are excluded there, and smooth W is excluded on the
way, inside `Erdos1017.CappedModel.SelectedHighLowStructure.remaining_benchmark_contact`,
by the root theorem of §10.1. The final dispatch
`Erdos1017.densityLimit_le_benchmark_of_cover` (`Erdos1017/FullBenchmarkUpper.lean`)
then splits the E₂ case at q ≤ 1/10 and at 1/5 ≤ q. The final case tree
therefore has five leaves: lower E₂, middle E₂ (the only one that uses the
cover certificate), upper E₂, the corner and the cusps. The six roots are:

| Contact | Root theorem | Location | Contact hypotheses |
|---|---|---|---|
| smooth W, §10.1 | `Erdos1017.CappedModel.SelectedHighLowStructure.no_smoothW_contact` | `Erdos1017/Exclusions/SmoothW/SelectedSmoothWExclusion.lean` | ε ∈ (ε*, ε_D), twoHeadCurve(ε) < mixedCurve(ε) |
| lower E₂, §10.2 | `Erdos1017.CappedModel.SelectedHighLowStructure.no_lowerE2_contact` | `Erdos1017/Exclusions/E2/Lower/SelectedLowerE2Exclusion.lean` | q ∈ (0, 1/10], d = (1 − h(q))/2 |
| upper E₂, §10.3 | `Erdos1017.CappedModel.SelectedHighLowStructure.no_upperE2_contact` | `Erdos1017/Exclusions/E2/Upper/SelectedUpperE2Exclusion.lean` | q ∈ [1/5, 213/1000], d as above, B(d) = twoHeadValue((q + 2)/3), B′(d) = −ℓ(q) |
| middle E₂, §10.4 | `Erdos1017.CappedModel.SelectedHighLowStructure.no_middle_e2_contact_of_cover` | `Erdos1017/Exclusions/E2/Middle/SelectedMiddleE2Exclusion.lean` | q ∈ (1/10, 1/5), d, value and derivative as above, `cover 80 IBox.root = true` |
| cusps, §10.5 | `Erdos1017.CappedModel.SelectedHighLowStructure.no_cusp_contact` | `Erdos1017/Exclusions/Cusp/SelectedCuspExclusion.lean` | k ≥ 3, d = (1 − 1/k²)/2 |
| corner, §10.6 | `Erdos1017.CappedModel.SelectedHighLowStructure.no_corner_global_excess` | `Erdos1017/Exclusions/Corner/SelectedCornerFinalExclusion.lean` | ε ∈ [ε_C, ε_D], twoHeadCurve(ε) = mixedCurve(ε) |

Each root concludes False from these and the standing hypotheses of §10.0;
the E₂ and cusp roots derive 1/4 < d < 1/2 from their parameter.

---

## 10.0 Common tools

`Erdos1017/Exclusions/Common/SelectedDiffuseIncidence.lean`, `Erdos1017/Exclusions/Common/SelectedRootRows.lean`, `Erdos1017/Exclusions/Common/Physical/PhysicalPositiveCover.lean`, `Erdos1017/Exclusions/Common/Flows/FullForwardQuarterFloor.lean`, `Erdos1017/Exclusions/Common/Flows/FullForwardSharpSelector.lean`, `Erdos1017/Exclusions/Common/Universal/SelectedUniversalNeutral.lean`, `Erdos1017/Exclusions/Common/Universal/UniversalCopyCubic.lean`, `Erdos1017/Exclusions/Common/Physical/IndependentAtomCopy.lean`, `Erdos1017/Exclusions/Common/Universal/SelectedUniversalPrimal.lean`, `Erdos1017/Exclusions/Common/Universal/SelectedTwoUniversalE2.lean`, `Erdos1017/Exclusions/Common/Universal/SelectedUniversalSATGeometry.lean`, `Erdos1017/Exclusions/Common/Universal/SelectedUniversalDeficitMass.lean`, `Erdos1017/Exclusions/Common/E2/SelectedEmptySatE2Inventory.lean`, `Erdos1017/Exclusions/Common/TwoCenter/SelectedOneCenterSourceCredit.lean`, `Erdos1017/Exclusions/Common/SelectedEmptySource.lean`, `Erdos1017/Exclusions/Common/TwoCenter/SelectedTwoCenterHeadPrice.lean`, `Erdos1017/Exclusions/Common/TwoCenter/SelectedTwoCenterAtomLocation.lean`, `Erdos1017/Exclusions/Common/Saturation/SelectedUnsaturatedZeroBody.lean`, `Erdos1017/Exclusions/Common/Covered/SelectedCoveredNullDiffuseDensity.lean`, `Erdos1017/Exclusions/Common/Covered/SelectedCoveredNoExterior.lean`, `Erdos1017/Exclusions/Common/Covered/SelectedCoveredBoundaryRepeat.lean`, `Erdos1017/Exclusions/Common/Covered/SelectedCoveredNeighborMultipartite.lean`, `Erdos1017/Exclusions/Common/Covered/SelectedCoveredFourRegionEntry.lean`, `Erdos1017/Exclusions/Common/Covered/SelectedCoveredOneExteriorCounts.lean`, `Erdos1017/Exclusions/Common/Covered/SelectedCoveredZeroExteriorCounts.lean`, `Erdos1017/Exclusions/Common/TwoAtom/TwoAtomContactGate.lean`, `Erdos1017/Exclusions/Common/Covered/CoveredOneExteriorGate.lean`, `Erdos1017/Exclusions/Common/Physical/PhysicalCountMeasure.lean`, `Erdos1017/Exclusions/Common/CliqueStarVariation.lean`, and 287 further modules under `Erdos1017/Exclusions/Common/`.

This section is a reference: the standing hypotheses, the objects attached
to the selected structure, and the tools that two or more of §10.1 to §10.6
cite. The one proof is that of the null-source bound c ≤ A_r².

**Standing hypotheses.** The roots of §10 are stated for a probability space
(Ω, μ) that is standard Borel with null singletons, compact metric with
its Borel σ-algebra, and has separable L²(μ); the lemmas need at most
these, and the final theorem takes [0, 1] with Lebesgue measure. The data W, m = −ℓ and
S : SelectedHighLowStructure W m satisfy (i) `FullStationaryClass d c W m`
(fully feasible, density d, objective c = F(d), M ∈ [0, 4], (1 − G)M = 0,
rows of M of integral ν, positive index at most two), (ii) 1/4 < d < 1/2
and c > B(d), and (iii) global maximality: objective(V) − B(density(V)) ≤
c − B(d) for every probability measure μ′ on Ω and every fully feasible V
on (Ω, μ′). Most tools use only (i) and (ii). Then ℓ > 0 and
γ = ν − ℓ = 2c − ℓh > 0 (§8).

| Symbol | Lean | Meaning |
|---|---|---|
| I_r, A_r | `Erdos1017.CappedModel.SelectedHighLowStructure.originalAtomMass` | the fiber {x : ρ(x) = r} of an atom r ∈ S.I (a positive independent set on which the row of M is the constant row r) and its mass μ(I_r); distinct atoms have A_r² + A_a² ≤ h (`Erdos1017.CappedModel.SelectedHighLowStructure.two_originalAtomMass_sq_le_missing_density`) |
| N(r) | `Erdos1017.CappedModel.SelectedHighLowStructure.rootNeighborhood` | points outside I_r where the row r is positive; up to null sets, the points joined to I_r |
| Y_r(x) | `Erdos1017.CappedModel.SelectedHighLowStructure.rootChargeRow` | the mean charge from I_r to x |
| Body(I) | `Erdos1017.PhysicalPrimal.bodyPositiveEnergy` | ∫∫ over (Ω ∖ I)² of max(Y, 0)²; zero (positive) body at r means Body(I_r) = 0 (> 0); equal to the physical form used by the traces (`Erdos1017.CappedModel.FullStationaryClass.bodyPositiveEnergy_eq_physicalBody`, §8) |
| H(r, p), U(r, p) | `Erdos1017.CappedModel.SelectedHighLowStructure.universalPartnerHoleRegion`, `Erdos1017.CappedModel.SelectedHighLowStructure.universalPartnerCommonRegion` | for a saturated pair, H = Ω ∖ (I_r ∪ I_p ∪ N(p)) and U = Ω ∖ (I_r ∪ I_p ∪ H); A_r + A_p + μ(H) + μ(U) = 1 (`Erdos1017.CappedModel.SelectedHighLowStructure.universalPartner_regions_mass`) |
| y | (none) | the deficit ratio 1 − 2γ/(1 − ℓ); Lean writes (1 − m − 4(c − md))/(1 + m) |

An atom r has the *universal row* if G = 0 on I_r × I_r and G = 1 on
I_r × (Ω ∖ I_r); it has the *private row against* p ≠ r if G = 0 on
I_r × (I_r ∪ I_p) and G = 1 on the rest of I_r × Ω. Recurring guards:
ℓ > 1/2 (covered reduction, shared two-centre mass); ℓ < 1 (saturation,
deficit ratio); the *copy bonus* A_r(1 − ℓ) < 2γ, supplied for every atom
by the guard lemmas of §10.1, §10.3, §10.5 and §10.6
(`Erdos1017.CappedModel.SelectedHighLowStructure.corner_atom_contact_guards`
for the corner); the *intercept guard*
(1 − ℓ)/4 < γ (two centres); and the *diffuse-cap guard* 2(1 − ℓ)A² < γ.

### Contact scalars

- **E₂ multiplier and γ floor** (`Erdos1017.CappedModel.FullStationaryClass.e2_gamma_floor`).
  If q ∈ (0, 1/5] and d = (1 − h(q))/2, then ℓ = ℓ(q) ∈ (0, 1) and
  γ > g(q). No value or derivative hypothesis is needed: B(d) =
  twoHeadValue((q + 2)/3) (`Erdos1017.Benchmark.benchmark_e2_q`), maximality
  gives ℓ = −B′(d) (`Erdos1017.CappedModel.FullStationaryClass.e2_contact_curvature`),
  and g(q) = 2B(d) − ℓ(q)h(q) (`Erdos1017.LowerE2Scalar.gapFloor_eq_twoHeadValue`),
  so γ − g(q) = 2(c − B(d)) > 0. Here d ∈ (1/4, 1/2) (`Erdos1017.Benchmark.e2_density_mem`).
- **Quarter peak** (`Erdos1017.CappedModel.SelectedHighLowStructure.exists_original_forward_quarter_peak`).
  For q ∈ [2/15, 1/5] the common forward peak i is HIGH or NEUTRAL, strictly
  the largest atom, with A_i > 1/4, the reserve γ + ℓ Σ_v A_v² ≤ 2A_i² (sum
  over all atoms v) and Σ_{v ≠ i} A_v² < A_i². For q < 2/15, §10.2 gives
  "A_i > 1/4 or universal".
- **Sharp selector bounds** (`Erdos1017.CappedModel.SelectedHighLowStructure.IsFullForwardFlow.endpoint_sharp_selector_bounds`).
  If a full forward flow has endpoint objective c_e, missing density h_e
  and top class of mass A, then c_e ≤ A² ≤ h_e, c_e ≤ min(1/9, h_e/3 + 1/27)
  if A ≤ 1/3, c_e ≤ (h_e + A²)/3 if A ≥ 1/3, plus two tail bounds. On a flow
  avoiding the peak (`Erdos1017.CappedModel.SelectedHighLowStructure.exists_fullForwardFlow_avoiding_atom`, §8)
  the top class has mass A_i and the endpoint budget gives γ ≤ 2c_e − ℓh_e.
- **Diffuse cap** (`Erdos1017.CappedModel.SelectedHighLowStructure.exists_conditional_missing_mass_cap`).
  With ϱ = √(((2 − ℓ)A_i² − γ)/ℓ) for the common peak i: every other HIGH
  atom has mass plus missing mass at most ϱ, and every other NEUTRAL atom
  mass at most ϱ. Only under the guard 2(1 − ℓ)A_i² < γ also ϱ < A_i,
  a.e. HIGH dust point has outside missing mass at most ϱ, and LOW atoms
  have mass at most ϱ (`Erdos1017.CappedModel.SelectedHighLowStructure.ae_diffuse_missing_le_radius_of_guard`).
  Each use supplies the guard: in the E₂ private branches from 2A_i² < 1/4
  and the intercept guard (`Erdos1017.CappedModel.FullStationaryClass.e2_intercept_guard`),
  in the large-head branch of §10.4 from A_i ≤ 369/1000 and
  γ > (631/2000)(1 − ℓ).

### The universal-peak toolkit

| Tool | Lean | Statement |
|---|---|---|
| universal atoms are neutral | `Erdos1017.CappedModel.SelectedHighLowStructure.universal_atom_neutral` | the universal row puts I_r a.e. in NEUTRAL; conversely a NEUTRAL atom has the universal row (`Erdos1017.CappedModel.SelectedHighLowStructure.neutral_atom_adjacency`, §8) |
| universal trace | `Erdos1017.CappedModel.SelectedHighLowStructure.universal_positive_body_trace` | I_r a.e. NEUTRAL and positive body at r give 3A_r² + 2A_rγ + γ² ≤ 2h |
| trace at a plateau peak | `Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.common_peak_head_positive_body_trace` | the same for a common forward peak in the plateau, with no NEUTRAL premise |
| universal physical primal | `Erdos1017.CappedModel.SelectedHighLowStructure.UniversalPhysicalPrimal` | a law on physical cliques of bounded order and cost c, each of charge exactly 1 with at most one vertex in I_r, root leaves A_r·μ on Ω ∖ I_r; a NEUTRAL atom has one (`Erdos1017.CappedModel.SelectedHighLowStructure.exists_universal_physical_primal`) |
| two universal heads | `Erdos1017.CappedModel.SelectedHighLowStructure.IsSaturatedAtomPair.not_both_universal_e2` | for q ∈ (0, 1/5], no saturated pair has both atoms universal |
| deficit ratio | `Erdos1017.CappedModel.SelectedHighLowStructure.universal_atom_mass_le_saturated_deficit_ratio` | (r, p) saturated, I_r a.e. NEUTRAL, ℓ < 1 and μ(H) > 0 give A_r ≤ y |
| hole inventory | `Erdos1017.CappedModel.SelectedHighLowStructure.empty_sat_small_parts_integrated_bounds` | same hypotheses, E = y − A_r, u = μ(U), L = μ(H) + u − y; if L > 0, E < L and the hole rows are *small* (a.e. x ∈ H has missing mass inside H below L), then L² ≤ E(y − u), EL + L² ≤ Eμ(H), L² ≤ Ey |
| root repricing | `Erdos1017.CappedModel.SelectedHighLowStructure.root_mass_le_cover_of_unsaturated_head` | if a positive set X lies a.e. in N(v) with Y_v < 1 on X and a.e. edge from X into N(v) ends in Z, then A_v ≤ μ(Z) |

The trace compares W with `Erdos1017.IndependentAtomCopy.charge`: one new
vertex copies an adjacent pair (x, y), with charge Y(x, z) + Y(y, z) +
Y(x, y)·1_{I_r}(z) to an old z. Optimality bounds the rows of the positive
body, orthogonal to the missing pairs outside I_r; a trace bound and the
missing-body energy h − A_r² conclude. The signed prices of §10.3, §10.4
and §10.6 are computed against the universal physical primal.

### Reverse-plateau geometry

A recovery has plateau P, height t and compulsory source S_P (§8).

| Tool | Lean | Statement |
|---|---|---|
| one-centre credit | `Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.singleton_source_credit` | if P = {r}: c + (ℓ/2)∫∫_{S_P×S_P} G + (1/2)∫∫_{S_P×S_P} M ≤ (A_r + μ(S_P))² |
| height | `Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.singleton_height_eq_mass_add_source` | if P = {r}: t = A_r + μ(S_P) |
| null source, peak | `Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.empty_source_is_original_peak` | if P = {r} and μ(S_P) = 0, r is the common forward peak and strictly the largest atom (a larger atom i would give h ≥ A_i² + A_r² > 2A_r² ≥ 2c > h, as B(d) ≥ h/2) |
| null source, neutral | `Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.empty_source_head_neutral` | the same r is NEUTRAL, hence universal; `Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.exists_empty_source_universal_peak` packages this with t = A_r and c ≤ A_r² |
| two centres | `Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.two_center_parameters` | if P has two atoms and (1 − ℓ)/4 < γ: 0 < ℓ < 1 and 1/3 < t ≤ 1/2 |
| large atoms sit on a head | `Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.original_atom_twoCenter_location` | if P = {r, u} and A_v > 1 − 2t, then I_v lies a.e. in I_r, in I_u, in a private source (of r or of u) or in the shared source |
| private atoms | `Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.private_atom_mass_lt_third` | under the intercept guard, an atom in a private source has mass below 1/3 |
| shared source | `Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.twoCenter_shared_mass_lt` | under the intercept guard and ℓ > 1/2, the shared source has mass below (1 − ℓ)/(4ℓ) < 1/4 |

- **Null source** (`Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.empty_source_objective_le_sq`, `Erdos1017/Exclusions/Common/SelectedEmptySource.lean`).
  If P = {r} and μ(S_P) = 0, then c ≤ A_r².
  - The set S_P × S_P has μ×μ-measure μ(S_P)² = 0, so the restricted
    measure on it is zero and both integrals in the one-centre credit
    vanish, while its right side is (A_r + 0)². The credit reads
    c ≤ A_r².
  - No maximality is used. The bound holds before the null-source case is
    excluded; branches that need positive source mass establish it apart.

### The covered-saturation reduction

This block excludes zero body at an atom r. Its exits assume ℓ > 1/2 and
the copy bonus at r (except the exit for at most one further atom), its
entries assume neither, and none uses contact data. D is the clique dust;
for a saturated partner a of r, R_a = D ∩ N(a) and E_a = D ∖ N(a).

| Zero body at r and | Conclusion | Lean |
|---|---|---|
| no saturated partner | impossible | `Erdos1017.CappedModel.SelectedHighLowStructure.not_zero_body_of_no_saturated_partner` |
| partner a, μ(D) = 0 | impossible | `Erdos1017.CappedModel.SelectedHighLowStructure.not_covered_null_diffuse` |
| R_a and E_a positive | every atom is r or a | `Erdos1017.CappedModel.SelectedHighLowStructure.covered_atoms_eq_root_or_saturated` |
| μ(D) > 0, R_a or E_a null, further atoms u ≠ v | every atom is r, a, u or v | `Erdos1017.CappedModel.SelectedHighLowStructure.covered_boundary_atoms_eq_four` |
| E_a null, at most one further atom | impossible | `Erdos1017.CappedModel.SelectedHighLowStructure.not_coveredNeighbor_boundary` |
| R_a, E_a positive, atoms r, a | block model on (I_a, I_r, R_a, E_a), feasible coefficients with positive head weight, same ℓ | `Erdos1017.CappedModel.SelectedHighLowStructure.exists_covered_four_region_entry` |
| R_a null, E_a positive, one exterior atom | block model with one exterior block (two-exterior and two-neighbour versions alongside) | `Erdos1017.CappedModel.SelectedHighLowStructure.exists_covered_one_exterior_entry` |
| R_a null, E_a positive, no exterior atom | j ≥ 1 with (j − 1)A_r ≤ μ(D) ≤ jA_r, block model with its own slope ℓ′ (multiplier −ℓ′) and charges (2/(j + 1), 2/(j(j + 1))) | `Erdos1017.CappedModel.SelectedHighLowStructure.exists_covered_zero_explicit_optimum` |

Each block model V is a new model on the same space, in the same class
FullStationaryClass d c, hence with the same density and objective
c = F(d); global maximality passes to it, but it is not W. The finite gates
`Erdos1017.TwoAtomCountGate.no_optimal_face_with_own_rows_moments` (four
blocks) and `Erdos1017.CoveredOneExterior.no_optimal_face_with_own_rows_moments`
(one exterior block) say that a block linear program has no optimal face
whose points carry their own count guards, stationary rows and tight
moments (moments of the clique-count law `Erdos1017.PhysicalPrimal.countMeasure`).
Each contact checks these hypotheses with its own gate lemmas (§10.1,
§10.3), which also include five-block gates for two exterior atoms and for
two neighbour atoms; the stationary V would lie on such a face.

---

## 10.1 Smooth W

`Erdos1017/Exclusions/SmoothW/SelectedSmoothWExclusion.lean`, `Erdos1017/Exclusions/SmoothW/FullSharpWPeak.lean`, `Erdos1017/Exclusions/SmoothW/SmoothWScalarExclusion.lean`, `Erdos1017/Exclusions/SmoothW/SelectedSmoothWPositiveBody.lean`, `Erdos1017/Exclusions/SmoothW/SelectedSmoothWAtomGuards.lean`, `Erdos1017/Exclusions/SmoothW/SelectedCoveredSmoothWContact.lean`, `Erdos1017/Exclusions/SmoothW/FullFreshIndependentStarCap.lean`, `Erdos1017/Exclusions/SmoothW/SelectedSmoothWRecovery.lean`, `Erdos1017/Exclusions/SmoothW/SelectedSmoothWEmptySource.lean`, `Erdos1017/Exclusions/SmoothW/SelectedSmoothWOneCenterGeometry.lean`, `Erdos1017/Exclusions/SmoothW/SelectedSmoothWOneCenterExclusion.lean`, `Erdos1017/Exclusions/SmoothW/SelectedSmoothWPrivateExclusion.lean`, `Erdos1017/Exclusions/SmoothW/SelectedSmoothWUniversalZeroBody.lean`, `Erdos1017/Exclusions/SmoothW/SelectedSmoothWZeroBody.lean`, `Erdos1017/Exclusions/SmoothW/SelectedSmoothWNeutralPeak.lean`, `Erdos1017/Exclusions/SmoothW/SelectedSmoothWTwoCenterLocations.lean`, `Erdos1017/Exclusions/SmoothW/SelectedSmoothWTwoCenter.lean`, `Erdos1017/Exclusions/SmoothW/TwoAtomSmoothWGate.lean`, `Erdos1017/Exclusions/SmoothW/CoveredOneExteriorSmoothWGate.lean`, `Erdos1017/Exclusions/SmoothW/CoveredTwoExteriorSmoothWGate.lean`, `Erdos1017/Exclusions/SmoothW/CoveredTwoNeighborSmoothWGate.lean`, and 13 further modules under `Erdos1017/Exclusions/SmoothW/`.

**Setting.** The standing hypotheses hold and the W branch strictly wins:
ε = 1/2 − d ∈ (ε*, ε_D) and twoHeadCurve(ε) < mixedCurve(ε). Put
σ = mixedInverse(ε). This contact reaches §10 from inside the contact
classification of §9, on the W branch of the family alternatives, before
the E₂ ranges are split; it is not one of the five final leaves.

**Shape of the argument.** Three numbers are read off the contact:
ℓ ∈ (1/2, 2/3), γ > 103/1000 and h < 1163/5000. The selector bounds then
make the common forward peak heavy, A > 357/1000, with γ < A. Every branch
of the case tree ends in one of three contradictions: a positive body at
a NEUTRAL peak violates the universal trace; a private hole violates the
fresh-star cap and the private trace; a zero body runs into the covered
reduction and a finite gate.

### The three numbers and the sharp peak

- **W slope** (`Erdos1017.Benchmark.benchmark_mixed_hasDerivAt_strict`). B is
  differentiable at d with B′(d) = −(σ + 1)/(3σ).
- **Contact parameters** (`Erdos1017.CappedModel.FullStationaryClass.smoothW_contact_parameters`).

      ℓ = (σ + 1)/(3σ),  σ ∈ (7/6, 19/15),  ℓ ∈ (1/2, 2/3),
      1 − ℓ < 101/250,  γ > 103/1000,  h < 1163/5000.

  - ℓ = −B′(d) by maximality at a smooth contact
    (`Erdos1017.CappedModel.full_stationary_multiplier_eq_benchmark_deriv`, §8);
    σ and h are bracketed by the family guards of §2, and
    ℓ = 1/3 + 1/(3σ) then lies in (34/57, 13/21).
  - With B(d) = mixedValue(σ) and h = 2·mixedDensity(σ),
    γ = 2c − ℓh > 2·mixedValue(σ) − ℓ·2·mixedDensity(σ), which exceeds
    103/1000 for σ ∈ [7/6, 19/15] (`Erdos1017.SmoothWScalar.mixed_intercept_gt`).
- **Sharp peak** (`Erdos1017.CappedModel.SelectedHighLowStructure.exists_sharp_smoothW_peak`).
  There is an atom i with A_i > 357/1000 and 103/1000 < γ < A_i; it is the
  separated common forward peak of every full forward flow, strictly the
  largest atom, and satisfies the square reserve.
  - Take the peak of §8 and a full forward flow avoiding it. The selector
    bounds of §10.0 give γ ≤ 2c_e − ℓh_e with top class mass A_i.
  - If A_i ≤ 1/3, then c_e ≤ 1/9 and 3c_e ≤ h_e + 1/9, and
    `Erdos1017.SmoothWScalar.selector_intercept_bound` (for ℓ ∈ [0, 2/3],
    C ≤ A² and 3C ≤ h_F + A² imply 2C − ℓh_F ≤ 2(1 − ℓ)A²) at A = 1/3 gives
    γ ≤ 2(1 − ℓ)/9 < 101/1125 < 103/1000, a contradiction.
  - So A_i > 1/3, and the same lemma gives γ ≤ 2(1 − ℓ)A_i² < (101/125)A_i².
    Hence A_i² > 103/808 > (357/1000)², and γ < A_i² ≤ A_i.
- **Peak guards** (`Erdos1017.CappedModel.SelectedHighLowStructure.smoothW_common_peak_guards`).
  Any common forward peak r is that atom (separated peaks are unique), so
  A_r > 357/1000, γ > 103/1000 and h < 1163/5000.
- **Atom guards** (`Erdos1017.CappedModel.SelectedHighLowStructure.smoothW_atom_contact_guards`,
  `Erdos1017.CappedModel.SelectedHighLowStructure.smoothW_covered_contact_guards`).
  Every atom r has A_r < 1/2 and the copy bonus A_r(1 − ℓ) < 2γ; the
  second lemma is the form used when a second atom is present.
- **Fresh-star cap** (`Erdos1017.CappedModel.FullStationaryClass.independent_set_mass_le_stationary`).
  A measurable a.e.-independent set Q satisfies (1 + ℓ)μ(Q) ≤ ν. The
  competitor adds a fresh vertex class joined exactly to Q, with charge 1
  on the new edges; since Q is independent every new clique is an edge, and
  comparing W with this competitor at small fresh mass, with the density
  restored by a reweighting, gives the bound.

### Case tree

- **Root** (`Erdos1017.CappedModel.SelectedHighLowStructure.no_smoothW_contact`). Take a recovery
  (`Erdos1017.CappedModel.SelectedHighLowStructure.exists_reverseRecovery`, §8).
  Its plateau has one or two atoms
  (`Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.smoothW_plateau_card_eq_one_or_two`),
  since ℓ > 1/2 and ε > ε* > 1/12
  (`Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.card_le_two_of_half_lt_neg_multiplier`, §8).
  - **One atom, null source** (`Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.no_smoothW_one_center_empty_source`).
    By `Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.exists_empty_source_universal_peak`
    (§10.0), P = {r} with r the common peak, NEUTRAL and universal.
    - Zero body at r: `Erdos1017.CappedModel.SelectedHighLowStructure.no_smoothW_zero_body` (subtree Z).
    - Positive body: `Erdos1017.CappedModel.SelectedHighLowStructure.no_smoothW_universal_peak_positive_body`.
  - **One atom, positive source** (`Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.no_smoothW_one_center_nonempty_source`).
    The sharp peak i and
    `Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.exists_smoothW_one_center_peak_geometry`
    give P = {p}, i ≠ p, and one of two patterns.
    - i has the private row against p:
      `Erdos1017.CappedModel.SelectedHighLowStructure.no_smoothW_private_common_peak`.
    - (i, p) is saturated and i has the universal row: i is NEUTRAL
      (`Erdos1017.CappedModel.SelectedHighLowStructure.universal_atom_neutral`).
      Zero body:
      `Erdos1017.CappedModel.SelectedHighLowStructure.no_smoothW_saturated_zero_body`
      at (i, p) (subtree Z′). Positive body:
      `no_smoothW_universal_peak_positive_body`.
  - **Two atoms** (`Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.no_smoothW_two_center`).
    The sharp peak r lies in P
    (`Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.smoothW_common_peak_mem_plateau`)
    and is NEUTRAL (`Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.common_peak_head_neutral`, §8);
    `Erdos1017.CappedModel.SelectedHighLowStructure.no_smoothW_neutral_common_peak`
    sends zero body to Z and positive body to the same leaf. No head-trace
    scalar is needed.
- **Subtree Z** (`no_smoothW_zero_body` at r). With no saturated partner,
  the atom guards and
  `Erdos1017.CappedModel.SelectedHighLowStructure.not_zero_body_of_no_saturated_partner`
  (§10.0) close. With a partner a, go to Z′.
- **Subtree Z′** (`no_smoothW_saturated_zero_body` at (r, a)), with
  R_a = D ∩ N(a), E_a = D ∖ N(a) and the covered guards. The dispatchers
  are `Erdos1017.CappedModel.SelectedHighLowStructure.no_smoothW_zero_body_E_null`
  (E_a null, R_a positive),
  `Erdos1017.CappedModel.SelectedHighLowStructure.no_smoothW_zero_body_of_E_positive`
  and `Erdos1017.CappedModel.SelectedHighLowStructure.no_smoothW_zero_body_R_null`.

| R_a | E_a | atoms other than r, a | leaf |
|---|---|---|---|
| null | null | any | `Erdos1017.CappedModel.SelectedHighLowStructure.no_smoothW_zero_body_of_D_null`, by `Erdos1017.CappedModel.SelectedHighLowStructure.not_covered_null_diffuse` |
| positive | null | at most one | `Erdos1017.CappedModel.SelectedHighLowStructure.not_coveredNeighbor_boundary` |
| positive | null | two or more, hence two | `Erdos1017.CappedModel.SelectedHighLowStructure.no_smoothW_zero_body_two_neighbor`, gate `Erdos1017.CoveredTwoExteriorNeighbor.no_smoothW_five_region` |
| null | positive | none | `Erdos1017.CappedModel.SelectedHighLowStructure.no_smoothW_zero_body_zero_exterior` |
| null | positive | one | `Erdos1017.CappedModel.SelectedHighLowStructure.no_smoothW_zero_body_one_exterior`, gate `Erdos1017.CoveredOneExterior.no_smoothW_one_exterior` |
| null | positive | two or more, hence two | `Erdos1017.CappedModel.SelectedHighLowStructure.no_smoothW_zero_body_two_exterior`, gate `Erdos1017.CoveredTwoExterior.no_smoothW_five_region` |
| positive | positive | none (by `Erdos1017.CappedModel.SelectedHighLowStructure.covered_atoms_eq_root_or_saturated`) | `Erdos1017.CappedModel.SelectedHighLowStructure.no_smoothW_zero_body_of_positive_regions`, then `Erdos1017.CappedModel.SelectedHighLowStructure.no_smoothW_zero_body_of_two_atoms`, gate `Erdos1017.TwoAtomCountGate.no_smoothW_four_region` |

"Two or more, hence two" uses
`Erdos1017.CappedModel.SelectedHighLowStructure.covered_boundary_atoms_eq_four`.

### The positive-body leaf, proved in full

- **Universal peak with positive body** (`Erdos1017.CappedModel.SelectedHighLowStructure.no_smoothW_universal_peak_positive_body`, `Erdos1017/Exclusions/SmoothW/SelectedSmoothWPositiveBody.lean`).
  Under the standing hypotheses and the smooth W contact, let r be a common
  forward peak with I_r a.e. NEUTRAL and positive body (in the physical
  form). Then False. All three plateau branches reach this leaf.
  - By the peak guards, A := A_r > 357/1000, γ > 103/1000 and
    h < 1163/5000.
  - By the universal trace (§10.0), 3A² + 2Aγ + γ² ≤ 2h.
  - The left side increases in A > 0 and γ > 0, so it exceeds

        3(357/1000)² + 2(357/1000)(103/1000) + (103/1000)² = 233249/500000,

    while 2h < 1163/2500 = 232600/500000. This is
    `Erdos1017.SmoothWScalar.not_trace_of_sharp_guards`; the margin is
    649/500000.

### The other leaves

- **Null source** (`no_smoothW_one_center_empty_source`). The null source
  gives c ≤ A_r², makes the plateau atom the common peak and makes it
  NEUTRAL (§10.0); its body is zero or positive, and the two subtrees above
  close the two cases.
- **Private peak** (`no_smoothW_private_common_peak`). The private row makes
  I_r ∪ I_u a.e. independent, so the fresh-star cap gives
  (1 + ℓ)(A_r + A_u) ≤ ν; with the sharp guards this forces A_u < γ < A_r.
  Then the strict private trace
  (`Erdos1017.CappedModel.SelectedHighLowStructure.private_body_strict_trace`)
  gives 3A_r² + 2A_rγ + γ² < 2h, which the same guards exclude.
- **One-centre geometry** (`exists_smoothW_one_center_peak_geometry`). The
  one-centre credit, with its two nonnegative source terms dropped, gives
  c ≤ t² = (A_p + μ(S_P))², and c > B(d) > 1/9 gives t > 1/3. The row of p
  integrates to ν, vanishes off N(p) and is at most 1 + ℓ, so
  μ(N(p)) ≥ ν/(1 + ℓ) > 1/3. Hence the region outside I_p ∪ S_P ∪ N(p), of
  mass 1 − t − μ(N(p)), is below 1/3 < A_i, and I_i lies a.e. in S_P,
  where its row is private against p, or in N(p). In the second case an
  unsaturated pair (i, p) would give 2A_i ≤ μ(N(p)) ≤ 1 − t < 2/3; so
  (i, p) is saturated, i is not HIGH (a saturated head has null HIGH part,
  `Erdos1017.CappedModel.SelectedHighLowStructure.IsSaturatedAtomPair.high_head_null`, §8),
  hence NEUTRAL and universal. The bound c ≤ t² is used here only to place
  t above 1/3.
- **Peak in a two-atom plateau** (`smoothW_common_peak_mem_plateau`). Since
  1 − ℓ < 101/250, the intercept guard holds (γ > 103/1000 > (1 − ℓ)/4);
  `Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.two_center_parameters`
  gives t > 1/3, so A_r > 357/1000 > 1 − 2t, and the location lemma leaves
  the two heads, because private atoms are below 1/3 and the shared source
  is below 1/4. A common peak in the plateau is NEUTRAL (§8), which feeds
  `no_smoothW_neutral_common_peak`.
- **Zero body without partner** (subtree Z). The copy bonus of the atom
  guards and ℓ > 1/2 are exactly the hypotheses of the §10.0 exit.
- **Zero exterior** (`no_smoothW_zero_body_zero_exterior`). The explicit
  block optimum V of §10.0 is a new model with an integer j and its own
  slope ℓ′. It has the density d and objective c of W, so global
  maximality passes to V, and the contact parameters applied to V give
  ℓ′ = (σ + 1)/(3σ) ∈ (1/2, 2/3). With this ℓ′, the row identity of V
  forces j = 2 (`Erdos1017.MixedContactIdentity.integer_contact_eq_two`);
  then the block masses, density and value of V are those of the W profile
  at σ, so c = B(d), against c > B(d).
- **Gates.** The four gate leaves of the table (the four-block gate, the
  one-exterior gate, and the five-block gates for two exterior atoms and
  for two neighbour atoms) check the gate hypotheses of §10.0 with
  ℓ ∈ (1/2, 2/3) and the block sizes of V.

---

## 10.2 Lower E₂, 0 < q ≤ 1/10

`Erdos1017/Exclusions/E2/Lower/FullLowerE2PeakIncidence.lean`, `Erdos1017/Exclusions/E2/Lower/FullLowerE2Saturation.lean`, `Erdos1017/Exclusions/E2/Lower/LowerE2PeakScalar.lean`, `Erdos1017/Exclusions/E2/Lower/LowerE2UniversalRatio.lean`, `Erdos1017/Exclusions/E2/Lower/OriginalMissingCrossInventory.lean`, `Erdos1017/Exclusions/E2/Lower/SelectedLowerE2Exclusion.lean`, `Erdos1017/Exclusions/E2/Lower/SelectedLowerE2NonuniversalQuarter.lean`, `Erdos1017/Exclusions/E2/Lower/SelectedLowerE2UniversalExclusion.lean`.

**Setting.** The standing hypotheses hold, with q ∈ (0, 1/10] and
d = (1 − h(q))/2. The root takes no value or derivative hypothesis: the
multiplier identity ℓ = ℓ(q) and the floor γ > g(q) are derived from
maximality by `Erdos1017.CappedModel.FullStationaryClass.e2_gamma_floor`
(§10.0). Densities just above 1/4 are E₂ points with small q, so there is
no separate low-density case. One argument covers all of (0, 1/10], in
three steps: the gap forces a heavy saturated pair; the largest atom is a
head of that pair; a universal saturated head with a positive hole has
y ≥ 8/25, while the E₂ floor caps y below 2/7.

- **Root** (`Erdos1017.CappedModel.SelectedHighLowStructure.no_lowerE2_contact`):
  `Erdos1017.CappedModel.SelectedHighLowStructure.exists_lowerE2_universal_saturated_peak`,
  then `Erdos1017.CappedModel.SelectedHighLowStructure.no_lowerE2_universal_saturated_peak`.
- **Heavy saturated pair** (`Erdos1017.CappedModel.FullStationaryClass.lowerE2_saturated_mass_floor`,
  `Erdos1017.CappedModel.SelectedHighLowStructure.exists_lowerE2_saturated_atoms`).
  (μ×μ){Y = 1}/2 > pairFloor(q), and some saturated pair (r, u) has
  A_rA_u > pairFloor(q).
- **The peak is a saturated head** (`exists_lowerE2_universal_saturated_peak`):
  there are atoms i, u with (i, u) saturated, i the common forward peak,
  strictly the largest, NEUTRAL and universal.
  - Take the peak i from the square reserve
    (`Erdos1017.CappedModel.SelectedHighLowStructure.exists_original_atomic_square_reserve`, §8)
    and the heavy pair (r, u). If i ∈ {r, u}, i has a partner.
  - Otherwise strict majority gives A_r² + A_u² < A_i², which
    `Erdos1017.CappedModel.SelectedHighLowStructure.IsSaturatedAtomPair.not_lowerE2_off_pair_majority`
    excludes. First, i is joined to both heads
    (`Erdos1017.CappedModel.SelectedHighLowStructure.IsSaturatedAtomPair.lowerE2_majority_atom_joined`):
    a whole missing block from I_i to I_r would give, by the cross inventory
    (`Erdos1017.CappedModel.SelectedHighLowStructure.original_squares_add_missing_cross_le`,
    sharpened under majority to
    `Erdos1017.CappedModel.SelectedHighLowStructure.thirtyThree_fifths_product_le_missing_density`),

        (33/5)A_rA_u ≤ h(q) < (33/5)·pairFloor(q)

    (`Erdos1017.LowerE2Scalar.missingMass_lt_thirtyThree_fifths_pairFloor`),
    against the pair floor. An atom joined to both heads has A_i ≤ y
    (`Erdos1017.CappedModel.SelectedHighLowStructure.IsSaturatedAtomPair.joined_atom_mass_bound`),
    and y < 9q/(2R(q)) < 2/7 as in the leaf below. But majority gives
    A_i² > 2A_rA_u > 2·pairFloor(q) > 4/49
    (`Erdos1017.LowerE2Scalar.pairFloor_gt_two_fortyNine`), so A_i > 2/7.
  - The peak is HIGH or NEUTRAL, and a saturated head has null HIGH part
    (`Erdos1017.CappedModel.SelectedHighLowStructure.IsSaturatedAtomPair.high_head_null`, §8);
    so it is NEUTRAL, hence universal
    (`Erdos1017.CappedModel.SelectedHighLowStructure.neutral_atom_adjacency`, §8).
- **Universal saturated peak** (`no_lowerE2_universal_saturated_peak`). Let
  (r, p) be saturated with r a NEUTRAL common peak, H = H(r, p).
  - μ(H) = 0: every point outside I_r ∪ I_p is then joined to p, and the
    saturated block joins I_r to I_p, so p is universal too;
    `Erdos1017.CappedModel.SelectedHighLowStructure.IsSaturatedAtomPair.not_both_universal_e2`
    (§10.0) closes.
  - μ(H) > 0: proved in full below.
- **The ratio floor** (`Erdos1017.CappedModel.SelectedHighLowStructure.saturated_ratio_ge_eight_twentyFifths`).
  If (r, p) is saturated, r a NEUTRAL common peak, ℓ < 1 and μ(H) > 0,
  then y ≥ 8/25. Suppose y < 8/25 and write A = A_r, b = A_p, u = μ(U).
  Then A ≤ y (deficit ratio, §10.0), b < A (r is strictly largest) and
  A + b + μ(H) + u = 1, so L = 1 − A − b − y > 0 and E = y − A < L. A
  point of H with positive missing mass inside H lies in a whole atom j
  inside H, with that missing mass equal to A_j. I_p lies in the missing
  set of I_j, so redirecting a forward flow through I_j and comparing with
  the separated peak gives A_j + b < A; as 2A + y < 1, A − b < L, and all
  hole rows are small. The hole inventory (§10.0) then gives
  (1 − A − b − y)² ≤ (y − A)(y − u), which
  `Erdos1017.UniversalDeficit.false_of_small_ratio_square` refutes for
  0 < A, b < A ≤ y < 8/25 and u ≥ 0.

### The positive-hole leaf, proved in full

- **Positive hole** (the case μ(H) > 0 of
  `Erdos1017.CappedModel.SelectedHighLowStructure.no_lowerE2_universal_saturated_peak`, `Erdos1017/Exclusions/E2/Lower/SelectedLowerE2UniversalExclusion.lean`).
  Let q ∈ (0, 1/10], d = (1 − h(q))/2, (r, p) saturated, r a NEUTRAL common
  forward peak and μ(H(r, p)) > 0. Then False.
  - By `e2_gamma_floor`, ℓ = ℓ(q) ∈ (0, 1) and γ > g(q); so the ratio
    floor applies and y ≥ 8/25.
  - The numerator of y is (1 − ℓ) − 2γ, which is below (1 − ℓ) − 2g(q).
    The identity `Erdos1017.LowerE2Scalar.deficit_eq_gap_mul_ratio` (for
    q ≥ 0)

        1 − ℓ(q) − 2g(q) = (1 − ℓ(q))·9q/(2R(q))

    rewrites the bound. Dividing by 1 − ℓ > 0 gives y < 9q/(2R(q)).
  - For q ∈ [0, 1/9], 9q/(2R(q)) < 2/7
    (`Erdos1017.LowerE2Scalar.ratio_lt_two_sevenths`, §11).
  - So 8/25 ≤ y < 2/7 < 8/25, a contradiction (8/25 − 2/7 = 6/175).

The leaf uses q ≤ 1/9 only; q ≤ 1/10 enters through the pair-floor scalars
of the off-pair step. This part also proves, for §10.3 and §10.4,
`Erdos1017.CappedModel.SelectedHighLowStructure.exists_original_e2_peak_quarter_or_universal`
(q ∈ (0, 2/15): the common peak is universal or has A > 1/4).

---

## 10.3 Upper E₂, 1/5 ≤ q ≤ 213/1000

`Erdos1017/Exclusions/E2/Upper/SelectedUpperE2Exclusion.lean`, `Erdos1017/Exclusions/E2/Upper/SelectedE2AtomGuards.lean`, `Erdos1017/Exclusions/E2/Upper/UpperE2ParameterGuards.lean`, `Erdos1017/Exclusions/E2/Upper/SelectedE2TwoCenter.lean`, `Erdos1017/Exclusions/E2/Upper/SelectedE2HeadTrace.lean`, `Erdos1017/Exclusions/E2/Upper/E2TwoCenterScalar.lean`, `Erdos1017/Exclusions/E2/Upper/SelectedE2PrivateExclusion.lean`, `Erdos1017/Exclusions/E2/Upper/SelectedUpperE2PeakThird.lean`, `Erdos1017/Exclusions/E2/Upper/SelectedE2EmptySource.lean`, `Erdos1017/Exclusions/E2/Upper/SelectedE2SaturatedEmptySource.lean`, `Erdos1017/Exclusions/E2/Upper/SelectedE2PrivateRadius.lean`, `Erdos1017/Exclusions/E2/Upper/SelectedUpperE2UnsaturatedPositiveBody.lean`, `Erdos1017/Exclusions/E2/Upper/SelectedUpperE2UniversalExclusion.lean`, `Erdos1017/Exclusions/E2/Upper/SelectedUpperE2OneCenterGeometry.lean`, `Erdos1017/Exclusions/E2/Upper/SelectedUpperE2PrivateExclusion.lean`, `Erdos1017/Exclusions/E2/Upper/SelectedUpperE2UniversalPriceJoin.lean`, `Erdos1017/Exclusions/E2/Upper/SelectedE2ZeroBody.lean`, `Erdos1017/Exclusions/E2/Upper/SelectedE2UnsaturatedZeroBody.lean`, `Erdos1017/Exclusions/E2/Upper/SelectedUpperE2PrivateRootStar.lean`, `Erdos1017/Exclusions/E2/Upper/SelectedUpperE2UniversalGeometry.lean`, and 30 further modules under `Erdos1017/Exclusions/E2/Upper/`.

**Setting.** The standing hypotheses hold with q ∈ [1/5, 213/1000] (closed),
d = (1 − h(q))/2, B(d) = twoHeadValue((q + 2)/3) and B′(d) = −ℓ(q). Unlike
§10.2, the root takes the value and derivative of B as hypotheses; §9
supplies them from `Erdos1017.Benchmark.strict_twoHead_contact_parameters`.

**Interval bookkeeping.** The root needs only [1/5, 213/1000], but its
plateau lemmas are proved on wider ranges because §10.4 reuses them through
`Erdos1017.CappedModel.SelectedHighLowStructure.exists_middle_e2_one_center_entry`:
the null-source lemma on (0, 213/1000], the two-centre lemma on
[1/10, 213/1000], the head-trace leaf on [1/10, 2/9] and the zero-body
subtree on (0, 2/9]. This is why some branches split again at q = 1/5.

- **Parameters** (`Erdos1017.CappedModel.FullStationaryClass.e2_general_contact_parameters`,
  `Erdos1017.CappedModel.SelectedHighLowStructure.e2_atom_contact_guards`,
  `Erdos1017.LowerE2Scalar.contact_density_mem`). For q ∈ (0, 2/9] with
  value and derivative contact: d ∈ (1/4, 1/2), ℓ = ℓ(q) ∈ (1/2, 1),
  γ > g(q), and every atom has A_r² ≤ h and the copy bonus.
- **Scalars on [1/5, 213/1000]** (`Erdos1017.UpperE2Parameter.missingMass_mem`,
  `Erdos1017.UpperE2Parameter.multiplier_mem`, `Erdos1017.UpperE2Parameter.gapFloor_ge`,
  `Erdos1017.UpperE2Parameter.twoHeadValue_gt`):
  h(q) ∈ (23/100, 3509/14884], ℓ(q) ∈ (4/5, 9/11], g(q) ≥ 7/122,
  B(d) > 123/1000. As ℓ ≥ 2/3, every plateau has at most two atoms
  (`Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.card_le_two_of_neg_multiplier_ge_two_thirds`, §8).
- **Two-centre scalars.** On (0, 2/9], (1 − ℓ(q))/4 < g(q), so the
  intercept guard holds (`Erdos1017.LowerE2Scalar.two_center_gapFloor_gt_quarter`),
  and g ≤ γ ≤ 2(1 − ℓ)t², γ ≤ (2 − ℓ)A² give 1 − 2t < A
  (`Erdos1017.LowerE2Scalar.two_center_outside_lt_peak`).

### Case tree

- **Root** (`Erdos1017.CappedModel.SelectedHighLowStructure.no_upperE2_contact`).
  Take a recovery; |P| ∈ {1, 2}.
  - **One atom, null source** (`Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.no_e2_one_center_empty_source`).
    - Saturated partner p: `Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.no_e2_saturated_empty_source`.
    - No partner: `Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.no_e2_unsaturated_empty_source`.
      For q ≤ 1/5 (needed by §10.4): c > B(d) > 1/8 and c ≤ A_r² give
      A_r > 1/3; with the intercept guard
      (`Erdos1017.CappedModel.FullStationaryClass.e2_intercept_guard`) and
      star charges below 1,
      `Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.entire_source_ne_zero_of_unsaturated_benchmark_ge_eighth`
      makes the source non-null. For q > 1/5: zero body goes to
      `Erdos1017.CappedModel.SelectedHighLowStructure.not_e2_zero_body_of_no_saturated_partner`,
      positive body to
      `Erdos1017.CappedModel.SelectedHighLowStructure.no_upper_e2_unsaturated_universal_positive_body`
      (the head is universal by
      `Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.empty_source_head_adjacency`).
  - **One atom, positive source** (`Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.no_upper_e2_one_center_positive_source`).
    `Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.exists_upper_e2_one_center_universal_sat_peak`
    gives P = {p} and a universal common peak i ≠ p saturated with p, with
    A_i > 1/3 and A_i < t = A_p + μ(S_P); i is NEUTRAL with a universal
    physical primal. Zero body: `Erdos1017.CappedModel.SelectedHighLowStructure.no_e2_zero_body`
    (subtree Z). Positive body:
    `Erdos1017.CappedModel.SelectedHighLowStructure.UniversalPhysicalPrimal.no_upper_e2_universal_positive_source`.
  - **Two atoms** (`Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.no_e2_two_center`).
    A common peak on the plateau is killed by
    `Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.no_e2_common_peak_head`,
    so it suffices to place the peak there. For q ≤ 1/5,
    `Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.exists_original_universal_e2_two_center_peak`
    gives a universal peak (from §10.2 for q < 2/15 and the quarter peak for
    q ≥ 2/15); the two-centre scalar gives 1 − 2t < A, and the location
    lemma leaves only the heads, a universal atom being NEUTRAL. For
    q > 1/5, A > 1/3 (`Erdos1017.CappedModel.SelectedHighLowStructure.exists_original_upper_e2_peak_gt_third`);
    `Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.two_center_parameters`
    gives t > 1/3, so 1 − 2t < 1/3 < A, and private atoms (below 1/3) and
    the shared source (below 1/4) are too small.
- **Subtree Z** (`no_e2_zero_body` at r, q ∈ (0, 2/9]). With no partner,
  `not_e2_zero_body_of_no_saturated_partner` reduces to the §10.0 exit.
  With a partner a, `Erdos1017.CappedModel.SelectedHighLowStructure.no_e2_saturated_zero_body`
  runs the covered reduction (dispatchers `Erdos1017.CappedModel.SelectedHighLowStructure.no_e2_zero_body_R_null`,
  `Erdos1017.CappedModel.SelectedHighLowStructure.no_e2_zero_body_R_null_of_E_positive`,
  `Erdos1017.CappedModel.SelectedHighLowStructure.no_e2_zero_body_E_null_of_R_positive`):

| R_a | E_a | atoms other than r, a | leaf |
|---|---|---|---|
| null | null | any | `Erdos1017.CappedModel.SelectedHighLowStructure.no_e2_zero_body_E_null`, by `Erdos1017.CappedModel.SelectedHighLowStructure.not_covered_null_diffuse` |
| null | positive | none | `Erdos1017.CappedModel.SelectedHighLowStructure.no_e2_zero_body_zero_exterior` |
| null | positive | one | `Erdos1017.CappedModel.SelectedHighLowStructure.no_e2_zero_body_one_exterior`, gate `Erdos1017.CoveredOneExterior.no_e2_one_exterior` |
| null | positive | two | `Erdos1017.CappedModel.SelectedHighLowStructure.no_e2_zero_body_two_exterior`, gate `Erdos1017.CoveredTwoExterior.no_e2_five_region` |
| positive | null | at most one | `Erdos1017.CappedModel.SelectedHighLowStructure.not_coveredNeighbor_boundary` |
| positive | null | two | `Erdos1017.CappedModel.SelectedHighLowStructure.no_e2_zero_body_two_neighbor`, gate `Erdos1017.CoveredTwoExteriorNeighbor.no_e2_five_region` |
| positive | positive | none | `Erdos1017.CappedModel.SelectedHighLowStructure.no_e2_zero_body_of_positive_regions`, then `Erdos1017.CappedModel.SelectedHighLowStructure.no_e2_zero_body_of_two_atoms` and the four-block gate |

### The head-trace leaf, proved in full

- **Common peak on a two-atom plateau** (`Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.no_e2_common_peak_head`, `Erdos1017/Exclusions/E2/Upper/SelectedE2HeadTrace.lean`).
  Let q ∈ [1/10, 2/9], d = (1 − h(q))/2, value and derivative contact, the
  standing hypotheses, a recovery with |P| = 2, and r ∈ P a common forward
  peak. Then False. This leaf closes the two-centre branch for
  q ∈ [1/10, 2/9] and uses no private geometry.
  - By the parameters, ℓ = ℓ(q) and γ ≥ g := g(q); write A = A_r. By
    subtree Z the body at r is not zero, so it is positive, also in
    physical form.
  - Head trace
    (`Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.common_peak_head_positive_body_trace`,
    §10.0): 3A² + 2Aγ + γ² ≤ 2h(q).
  - Head budget (`Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.common_peak_head_square_budget`, §8):
    with two plateau atoms, γ ≤ 2(1 − ℓ)A².
  - These contradict `Erdos1017.LowerE2Scalar.not_two_center_head_trace`.
    Put X = g/(2(1 − ℓ(q))) = (q + 2)(2q + 1)/(8R(q)) and
    V = 2h(q) − 3X − g². The budget and γ ≥ g give X ≤ A². The trace gives

        2Ag ≤ 2Aγ ≤ 2h − 3A² − γ² ≤ 2h − 3X − g² = V,

    so V ≥ 0 and V² ≥ 4A²g² ≥ 4g²X. But

        4g²X − V² = Ψ(q)/(64R(q)⁴),
        Ψ(q) = −80q⁸ − 456q⁷ − 793q⁶ + 630q⁵ + 2173q⁴ + 674q³ − 349q² + 68q − 4,

    and Ψ > 0 on [1/10, 2/9]: in the variable x = (90q − 9)/11 ∈ [0, 1] its
    nine Bernstein coefficients are at least 1/100.

### The one-centre leaves

The positive-source case is the heart of the range.

- **Location** (`exists_upper_e2_one_center_universal_sat_peak`). The peak i
  has A_i > 1/3, and the one-centre geometry leaves "i private against p"
  or "(i, p) saturated with i universal". The private case is
  `Erdos1017.CappedModel.SelectedHighLowStructure.no_upper_e2_private_common_peak`:
  i is HIGH, N(i) is up to null sets the complement of I_i ∪ I_p
  (`Erdos1017.CappedModel.SelectedHighLowStructure.ae_private_rootNeighborhood_iff`),
  and the scalar exits `Erdos1017.UpperE2PrivateScalar.saturated_false`,
  `Erdos1017.UpperE2PrivateScalar.unsaturated_small_b_false` and
  `Erdos1017.UpperE2PrivateScalar.unsaturated_large_b_false` close it.
- **Signed price** (`no_upper_e2_universal_positive_source`). Let (r, p) be
  the saturated pair with r the universal peak, A = A_r, b = A_p and
  u = μ(U(r, p)). On the negative region (the points of U(r, p) where the
  root charge row Y_r is negative), the tight universal physical primal at
  r and a signed copy of the partner row bound the charge from I_r
  pointwise. Integrated over that region, this gives one linear inequality
  between the negative charge mass ∫(−Y_r), the region's mass and two
  moments weighted by −Y_r: of the mass of the atom containing the point
  (zero on dust), and of its missing mass into the good common region,
  which is U(r, p) minus
  `Erdos1017.CappedModel.SelectedHighLowStructure.universalUpperE2BadRegion`
  (the points outside I_r ∪ I_p where Y_r < 3γ/A_r − (1 − ℓ); §10.4 and
  §10.6 reuse this region). The right side is a reciprocal allowance
  weighted by max(bℓ − γ, 0) plus calibration terms, and the moments are
  capped by a shared-hole radius z and by
  min(1 − 3A + b, (1 − u − 2ℓA − 3γ)/ℓ).
  If bℓ ≥ γ, the inequality makes a scalar price nonnegative, against
  `Erdos1017.UpperE2UniversalScalar.originalPrice_neg`; that lemma rests on
  the certified sign `Erdos1017.UpperE2UniversalScalar.enlargedF_neg` (§11)
  and on the packing bound q_H + z² ≤ 3509/14884 − A² − b² −
  2b(1 − A − b − u) for the square moment q_H of the hole rows. If bℓ < γ,
  then b < 1/8 and the inequality fails directly.
- **Unsaturated universal peak** (`no_upper_e2_unsaturated_universal_positive_body`).
  A > 1/3; the trace with h(q) ≤ 3509/14884 gives A < 2/5; with star
  charges below 1 and (1 − ℓ)(1 − A) < 3γ, the half-root quota
  (`Erdos1017.CappedModel.SelectedHighLowStructure.unsaturated_universal_objective_le_half_root_quota`)
  gives c ≤ A(1 − A)/2 < 3/25 < 123/1000 < B(d) < c.
- **Saturated null source** (`no_e2_saturated_empty_source`). The head r is a
  NEUTRAL peak with c ≤ A_r² and A_p < A_r. With E = y − A_r and
  L = μ(H) + μ(U) − y as in §10.0, there are three exits: L ≤ E
  (`Erdos1017.EmptySatE2.supportScore_pos_of_le_excess`); E < L with small
  hole rows, through the hole inventory
  (`Erdos1017.EmptySatE2.integratedScore_pos`); and a whole atom in H with
  missing mass at least L (`Erdos1017.EmptySatE2.rawExceptionalScore_pos`).
  The same three-way split, with corner constants, is the sector table of
  §10.6.

---

## 10.4 Middle E₂, 1/10 < q < 1/5

`Erdos1017/Exclusions/E2/Middle/SelectedMiddleE2Exclusion.lean`, `Erdos1017/Exclusions/E2/Middle/SelectedMiddleSaturatedDichotomy.lean`, `Erdos1017/Exclusions/E2/Middle/SelectedMiddleUnsaturatedExclusion.lean`, `Erdos1017/Exclusions/E2/Middle/SelectedMiddlePrivateSoleSource.lean`, `Erdos1017/Exclusions/E2/Middle/SelectedMiddlePrivateSoleSourceExposure.lean`, `Erdos1017/Exclusions/E2/Middle/SelectedMiddleOffPairDominance.lean`, `Erdos1017/Exclusions/E2/Middle/SelectedMiddleOffPairThird.lean`, `Erdos1017/Exclusions/E2/Middle/SelectedMiddleOffPairCompulsory.lean`, `Erdos1017/Exclusions/E2/Middle/SelectedUniversalE2SmallHead.lean`, `Erdos1017/Exclusions/E2/Middle/SelectedMiddleLargeUniversalGuards.lean`, `Erdos1017/Exclusions/E2/Middle/SelectedMiddleLargeUniversalSystem.lean`, `Erdos1017/Exclusions/E2/Middle/SelectedMiddleLargeUniversalPrice.lean`, `Erdos1017/Certificates/MiddleE2LargeUniversal/MiddleE2LargeUniversalContract.lean`, `Erdos1017/Exclusions/E2/Middle/SelectedMiddleSaturatedPrivateExclusion.lean`, `Erdos1017/Exclusions/E2/Middle/SelectedMiddleSaturatedPrivateStarsPositive.lean`, and 53 further modules under `Erdos1017/Exclusions/E2/Middle/` and `Erdos1017/Certificates/MiddleE2LargeUniversal/`.

**Setting.** The *middle contact* is the hypothesis bundle: the standing
hypotheses, q ∈ (1/10, 1/5), d = (1 − h(q))/2,
B(d) = twoHeadValue((q + 2)/3) and B′(d) = −ℓ(q). Then ℓ = ℓ(q) and
γ > g(q) (`Erdos1017.CappedModel.FullStationaryClass.e2_general_contact_parameters`),
and ℓ(q) > ℓ(1/5) = 9/11 since q < 1/5. The root also takes the Boolean
premise that the fixed-point cover succeeds; the final assembly discharges
it with `Erdos1017.MiddleE2LargeUniversal.FixedPoint.cover_root` (§11).

**Three branches.** The root never splits on q. It calls one dichotomy
and dispatches on its output:

| Branch | Configuration | Lower bound on q forced inside | Closed by | Certificate |
|---|---|---|---|---|
| unsaturated | no saturation, (μ×μ){Y = 1} = 0 | q > 187/1000 | sole-source residual against exposure | no |
| large head | the peak is a head of the saturated pair, universal, A > 1/3 | q > 157/1000 | price tests at the point (q, A, b, u) | yes |
| private | the peak is off the pair, with the private row against a head | q > 19/160 | positive stars and curvature | no |

The value q = 19/160 is not a split of the root. It is derived by
contradiction twice: inside the dichotomy (an off-pair peak forces
q > 19/160) and again inside the private branch. The large-head branch is
the only place in §10 that uses the computer certificate, and it uses it
at one point read off the model.

### The common one-centre entry

- **Entry** (`Erdos1017.CappedModel.SelectedHighLowStructure.exists_middle_e2_one_center_entry`).
  Under the middle contact: ℓ(q) > 9/11, γ > g(q), d > 1/3, and there are
  a recovery with plateau {p} and positive source and a common forward peak
  i ≠ p, strictly the largest atom with the square reserve, such that
  either I_i lies a.e. in S_P with the private row of i against p, or I_i
  lies a.e. in N(p).
  - Since ℓ ≥ 2/3 the plateau has at most two atoms; two atoms are
    excluded by `Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.no_e2_two_center`
    and a null source by
    `Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.no_e2_one_center_empty_source`
    (§10.3, whose ranges cover (1/10, 1/5)).
  - The peak is not the plateau atom, because the source is positive and a
    common peak in the plateau has mass equal to the height.
  The entry feeds the large-head branch (the recovery with plateau {p} at
  the partner of the universal peak), the bound A < 1/3 of an off-pair
  peak, and the source peak of the unsaturated branch.

### The dichotomy and the root

- **Root** (`Erdos1017.CappedModel.SelectedHighLowStructure.no_middle_e2_contact_of_cover`).
  From the dichotomy: in case (a),
  `Erdos1017.CappedModel.SelectedHighLowStructure.middle_large_universal_necessary_system`
  gives a point in the box satisfying the necessary system, the cover gives
  the price tests (`Erdos1017.MiddleE2LargeUniversal.FixedPoint.priceTests_of_cover`),
  and `Erdos1017.CappedModel.SelectedHighLowStructure.no_middle_large_universal_of_price_tests`
  closes; in case (b),
  `Erdos1017.CappedModel.SelectedHighLowStructure.no_middle_saturated_private_contact`
  closes.
- **Dichotomy** (`Erdos1017.CappedModel.SelectedHighLowStructure.exists_middle_saturated_dichotomy`).
  Under the middle contact there is a common forward peak i and either
  (a) a saturated pair (i, p) with A_i > 1/3, I_i NEUTRAL and the universal
  row; or (b) a saturated pair (p, u) with i ∉ {p, u}, q > 19/160,
  A_i ∈ (1/4, 1/3), A_i ≤ y < 9q/(2R(q)), I_i HIGH and inside the compulsory
  source of {p}, and the private row of i against p.
  - Saturation is positive: otherwise the unsaturated branch
    (`Erdos1017.CappedModel.SelectedHighLowStructure.no_middle_unsaturated_contact`)
    gives False. So there is a saturated pair (r, u)
    (`Erdos1017.CappedModel.SelectedHighLowStructure.exists_saturated_atom_pair_of_positive_mass`, §8),
    and the peak i comes from the square reserve
    (`Erdos1017.CappedModel.SelectedHighLowStructure.exists_original_atomic_square_reserve`, §8).
  - If i ∈ {r, u}: i is NEUTRAL
    (`Erdos1017.CappedModel.SelectedHighLowStructure.IsSaturatedAtomPair.high_head_null`),
    universal, and A_i > 1/3 because a universal saturated peak with
    A ≤ 1/3 is impossible for q ∈ (0, 1/5]
    (`Erdos1017.CappedModel.SelectedHighLowStructure.no_universal_e2_small_head_saturated_peak`).
    That lemma has three exits, which overlap at their endpoints: q ≤ 7/50
    (`Erdos1017.CappedModel.SelectedHighLowStructure.no_universal_middle_small_parameter_saturated_peak`),
    7/50 ≤ q ≤ 157/1000
    (`Erdos1017.CappedModel.SelectedHighLowStructure.no_universal_middle_low_parameter_saturated_peak`),
    both for every mass, and q > 157/1000 with A ≤ 1/3
    (`Erdos1017.CappedModel.SelectedHighLowStructure.no_universal_middle_small_head_saturated_peak`).
  - If i ∉ {r, u}: for q ≤ 19/160 the peak would be a head
    (`Erdos1017.CappedModel.SelectedHighLowStructure.middle_e2_common_peak_mem_saturated_pair`,
    on [1/10, 19/160]), so q > 19/160. Further A_i < 1/3
    (`Erdos1017.CappedModel.SelectedHighLowStructure.middle_e2_off_pair_peak_lt_third`),
    A_i ≤ y < 9q/(2R(q))
    (`Erdos1017.CappedModel.SelectedHighLowStructure.middle_e2_off_pair_peak_bounds`),
    i lies in the source of a head p and has the private row against it
    (`Erdos1017.CappedModel.SelectedHighLowStructure.middle_e2_off_pair_private_row`),
    so it is HIGH, and a HIGH peak has A_i > 1/4
    (`Erdos1017.CappedModel.SelectedHighLowStructure.middle_e2_high_common_peak_quarter`).
    The pair is oriented with the private head first.

### The unsaturated branch, proved in full

- **No saturation** (`Erdos1017.CappedModel.SelectedHighLowStructure.no_middle_unsaturated_contact`, `Erdos1017/Exclusions/E2/Middle/SelectedMiddleUnsaturatedExclusion.lean`).
  Under the middle contact, (μ×μ){Y = 1} = 0 is impossible.

  Let K = (Ω ∖ (I_i ∪ I_p)) ∖ N(p) denote the *hole* of a pair of atoms
  (i, p): the points outside both fibers not joined to p. Write M_i for the
  constant M-row of the atom i.

  - **Residual** (`Erdos1017.CappedModel.SelectedHighLowStructure.exists_middle_unsaturated_sole_source_residual`).
    With no saturation: ℓ = ℓ(q), q > 187/1000, and there are a recovery
    with plateau {p} and a common forward peak i ≠ p such that
    61/200 < A_i < 1/3, I_i lies a.e. in S_P, i has the private row against
    p, S_P ∖ I_i is null (the peak is the sole source), and

        ∫_K M_i dμ ≤ ℓ μ(K).

  - **Exposure** (`Erdos1017.CappedModel.SelectedHighLowStructure.middle_private_sole_source_exposure`).
    For atoms i ≠ p with no saturation, i a common forward peak, I_i a.e.
    in the source of {p} and the private row of i against p:

        ℓ μ(K) < ∫_K M_i dμ.

  - The residual supplies exactly the hypotheses of the exposure lemma (the
    same i, p, the source inclusion and the private row), and the two
    displays are incompatible.

  The residual is assembled from four results. The one-centre entry with
  the joined alternative excluded
  (`Erdos1017.CappedModel.SelectedHighLowStructure.exists_middle_unsaturated_source_peak_actual`)
  gives q > 187/1000, a positive source, a peak with A_i > 3/10 in it and
  the private row. The peak bounds
  (`Erdos1017.CappedModel.SelectedHighLowStructure.middle_private_peak_bounds`)
  give 61/200 < A_i < 1/3. A second source atom or dust of positive mass is
  excluded
  (`Erdos1017.CappedModel.SelectedHighLowStructure.no_middle_private_positive_secondary_source`).
  Finally, if ℓμ(K) < ∫_K M_i, the scaled curvature bound, the sole-source
  cost c ≤ (A_i + A_p)², the flat head row and a closed scalar inequality
  contradict each other
  (`Erdos1017.CappedModel.SelectedHighLowStructure.no_middle_private_sole_source_of_exposure`),
  which gives the displayed inequality. On K the private row gives G = 1
  from I_i, so M_i is the mean charge from I_i plus ℓ there, and the
  exposure lemma says that this mean charge has positive integral over K.
  It is proved with a physical primal adapted to the private row, which
  shows the charge from I_i to be positive a.e. on K, first on the dust of
  K and then on its atoms. This branch needs neither the certificate nor the
  19/160 cut.

### The large-head branch

- **Initial guards** (`Erdos1017.CappedModel.SelectedHighLowStructure.middle_large_universal_initial_guards`).
  For a saturated pair (r, p) with r a universal common peak: a universal
  physical primal at r exists, q > 157/1000, A = A_r ∈ (1/3, 369/1000),
  μ(H(r, p)) > 0, ℓ ∈ (4/5, 1), γ > g(q), A ≤ y < 9q/(2R(q)) ≤ 45/122,
  b = A_p ∈ (0, 1/3), b ≤ 1 − 2A, 0 ≤ u = μ(U(r, p)) ≤ 1 − A − b and
  2A(1 − ℓ) < 3γ.
  - q > 157/1000 is the contrapositive of the first two small-head exits,
    and A > 1/3 of the third.
  - μ(H) > 0 because otherwise the partner would be universal too
    (`Erdos1017.CappedModel.SelectedHighLowStructure.IsSaturatedAtomPair.not_both_universal_e2`, §10.0);
    then A ≤ y by the deficit ratio, and
    y < 9q/(2R(q)) ≤ 45/122 < 369/1000 by the E₂ floor.
  - Every point of H has degree at least 2A and at most 1 − b, which gives
    b ≤ 1 − 2A; the margin 2A(1 − ℓ) < 3γ follows from y < 369/1000.
- **The certificate point** (`Erdos1017.CappedModel.SelectedHighLowStructure.middleLargeUniversalPoint`).
  The point (q, A, b, u) of the model, an element of
  `Erdos1017.MiddleE2LargeUniversal.Point` with its derived quantities (ℓ,
  g, h, y and the price terms).
- **Necessary system** (`middle_large_universal_necessary_system`). For the
  same pair there are a universal physical primal, a recovery with plateau
  {p} and positive source, and the point satisfies
  `Erdos1017.MiddleE2LargeUniversal.Point.InBox`
  (157/1000 ≤ q ≤ 1/5, 1/3 ≤ A ≤ 369/1000, 0 ≤ b, u ≤ 1/3) and
  `Erdos1017.MiddleE2LargeUniversal.Point.Necessary` (sixteen inequalities
  that every such model satisfies). The diffuse-cap guard is supplied here
  (§10.0).
- **Cover** (`Erdos1017.MiddleE2LargeUniversal.FixedPoint.priceTests_of_cover`, `Erdos1017/Certificates/MiddleE2LargeUniversal/MiddleE2LargeUniversalCertificateSound.lean`).
  If `cover 80 IBox.root = true`, every point that is InBox and Necessary
  satisfies `Erdos1017.MiddleE2LargeUniversal.Point.PriceTests`: six strict
  positivity conditions (the pole, u, R_P, the moment, the zero price and
  g − E) and G < 0. The arithmetic is in `certificates.md`.
- **Price** (`no_middle_large_universal_of_price_tests`). For the model's
  own point, Necessary and PriceTests are contradictory: the signed price
  computed from the universal physical primal is positive, while the price
  tests bound it above by the certificate price G < 0.

So the certificate is used once, at the single point read off the model,
and only in this branch. (In the price tests, R_P, E and G are the
certificate's own quantities, not the dust region R_a, the excess or the
adjacency.)

### The private branch

- **Private peak** (`no_middle_saturated_private_contact`). Let (u, v) be
  saturated and i ∉ {u, v} a common peak with the private row against u.
  - It first rederives q > 19/160: for q ≤ 19/160 the common peak is a head
    of a saturated pair
    (`Erdos1017.CappedModel.SelectedHighLowStructure.middle_e2_common_peak_universal_cutoff`),
    and by uniqueness of the saturated pair
    (`Erdos1017.CappedModel.SelectedHighLowStructure.IsSaturatedAtomPair.unique`, §8)
    that head is u or v.
  - Positive stars: for q ∈ [19/160, 1/5], Y_i > 0 a.e. on the hole
    (Ω ∖ (I_i ∪ I_u)) ∖ N(u)
    (`Erdos1017.CappedModel.SelectedHighLowStructure.ae_middle_saturated_private_star_pos`).
    The peak is HIGH, a sharp radius bounds the missing mass around it, and
    a physical primal pays an insertion at every hole point.
  - Closing (`Erdos1017.CappedModel.SelectedHighLowStructure.no_middle_saturated_private_of_positive_stars`).
    The peak has 1/4 < A_i < 1/3. Positive stars make the hole exposure
    strict; the E₂ curvature bound of
    `Erdos1017.CappedModel.FullStationaryClass.e2_contact_curvature` (with
    curvature coefficient in (0, 6), `Erdos1017.E2PrivateCurvature.curvature_pos_lt_six`,
    §11) gives a scaled covariance inequality
    (`Erdos1017.CappedModel.SelectedHighLowStructure.private_curvature_covariance_scaled`);
    the unique saturated pair gives a score bound
    (`Erdos1017.CappedModel.SelectedHighLowStructure.middle_saturated_private_score`);
    and with the row margin these inequalities are incompatible
    (`Erdos1017.MiddleSaturatedPrivateScalar.saturated_private_false`).

---

## 10.5 Reciprocal cusps, k ≥ 3

`Erdos1017/Exclusions/Cusp/SelectedCuspExclusion.lean`, `Erdos1017/Exclusions/Cusp/SelectedCuspLargeExclusion.lean`, `Erdos1017/Exclusions/Cusp/SelectedCuspFiveExclusion.lean`, `Erdos1017/Exclusions/Cusp/SelectedCuspFourExclusion.lean`, `Erdos1017/Exclusions/Cusp/SelectedCuspThreeExclusion.lean`, `Erdos1017/Exclusions/Cusp/SelectedCuspThreeHighExclusion.lean`, `Erdos1017/Exclusions/Cusp/SelectedCuspAtomGuards.lean`, `Erdos1017/Exclusions/Cusp/SelectedCuspPositiveSource.lean`, `Erdos1017/Exclusions/Cusp/SelectedCuspRecoveryBounds.lean`, `Erdos1017/Exclusions/Cusp/SelectedCuspSourceChild.lean`, `Erdos1017/Exclusions/Cusp/SelectedCuspSourcePeak.lean`, `Erdos1017/Exclusions/Cusp/SelectedCuspOutsidePeak.lean`, `Erdos1017/Exclusions/Cusp/CuspOutsidePeakScalar.lean`, `Erdos1017/Exclusions/Cusp/SelectedCuspFiveSourcePeak.lean`, `Erdos1017/Exclusions/Cusp/SelectedCuspFiveOutsidePeak.lean`, `Erdos1017/Exclusions/Cusp/SelectedCuspFourSourcePeak.lean`, `Erdos1017/Exclusions/Cusp/SelectedCuspFourOutsidePeak.lean`, `Erdos1017/Exclusions/Cusp/SelectedCuspThreeHighSourcePeak.lean`, `Erdos1017/Exclusions/Cusp/SelectedCuspThreeOutsidePeak.lean`, `Erdos1017/Exclusions/Cusp/SelectedCuspThreeLowSlopeUniversal.lean`, `Erdos1017/Exclusions/Cusp/SelectedCuspThreeMissingInventory.lean`, `Erdos1017/Exclusions/Cusp/SelectedCuspThreeDominantMissing.lean`, `Erdos1017/Exclusions/Cusp/SelectedCuspThreeDispersedMissing.lean`, and 81 further modules under `Erdos1017/Exclusions/Cusp/`.

**Setting.** The standing hypotheses hold at d = (1 − 1/k²)/2 with k ≥ 3,
that is √(1 − 2d) = 1/k, where B has a kink with value (k − 1)/k³ and
h = 1/k². Put

    L_k = 2 − 2/k − 2/(k + 1),   U_k = 2 − 2/k.

These are −1 times the slopes of the left and right split extensions at
the kink (§9). The first cusps:

| k | d | h = 1/k² | B(d) = (k − 1)/k³ | L_k | U_k |
|---|---|---|---|---|---|
| 3 | 4/9 | 1/9 | 2/27 | 5/6 | 4/3 |
| 4 | 15/32 | 1/16 | 3/64 | 11/10 | 3/2 |
| 5 | 12/25 | 1/25 | 4/125 | 19/15 | 8/5 |
| 6 | 35/72 | 1/36 | 5/216 | 29/21 | 5/3 |

- **Slope bracket** (`Erdos1017.CappedModel.FullStationaryClass.cusp_contact_parameters`).
  There is no derivative at a cusp; the multiplier lies strictly between the
  one-sided slopes (§9):

      d ∈ (1/4, 1/2),  ℓ ∈ (L_k, U_k) ∩ (5/6, 2),  γ > 0,  (U_k − ℓ)/k² < γ.

  The last inequality is c > B(d): since γ = 2c − ℓ/k², it reads
  2c > 2(k − 1)/k³.
- **Atom guards** (`Erdos1017.CappedModel.SelectedHighLowStructure.cusp_atom_contact_guards`).
  Every atom has A_r² ≤ 1/k², so A_r ≤ 1/k, and the copy bonus.

**Why k = 3 splits.** L_3 = 5/6 < 1 < 4/3 = U_3, so at k = 3 the slope may
lie on either side of 1, and the root splits at ℓ = 1 (the endpoint ℓ = 1
going to the high side). For k ≥ 4, ℓ > L_4 = 11/10 > 1, so every plateau
has |P| < 2/ℓ < 2 atoms: it is a single atom.

### The common skeleton

For k ≥ 4, and for k = 3 with ℓ ≥ 1, the exclusion runs as follows.

1. A recovery exists
   (`Erdos1017.CappedModel.SelectedHighLowStructure.exists_reverseRecovery`, §8).
2. Its plateau is one atom {r}
   (`Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.cusp_plateau_singleton`
   for k ≥ 4; `Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.cusp_three_plateau_singleton`
   for k = 3, ℓ ≥ 1).
3. Its height exceeds 1/k
   (`Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.cusp_height_gt_reciprocal`;
   `Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.cusp_three_height_gt_third`).
4. The common peak i (square reserve, §8) is not r: a common peak in the
   plateau has A_r = t
   (`Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.common_peak_head_mass`, §8),
   but A_r ≤ 1/k < t.
5. Membership of I_i in the compulsory source
   (`Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.cuspSource`)
   is a.e. constant on I_i, decided by a fiber predicate
   (`Erdos1017.CappedModel.SelectedHighLowStructure.ae_compulsorySource_iff_fiberPredicate`).
   So either I_i lies a.e. in the source, or a.e. outside I_r ∪ S_P.
6. The source leaf and the outside leaf for that k close the two cases.

### The template, proved in full

- **Cusps with k ≥ 6** (`Erdos1017.CappedModel.SelectedHighLowStructure.no_cusp_contact_of_six_le`, `Erdos1017/Exclusions/Cusp/SelectedCuspLargeExclusion.lean`).
  Under the standing hypotheses at d = (1 − 1/k²)/2 with k ≥ 6: False.
  - The bracket gives d ∈ (1/4, 1/2), so a recovery exists.
  - Since k ≥ 4, its plateau is {r} and t > 1/k.
  - Let i be the common forward peak. If i = r, then A_r = t because a
    common peak in the plateau keeps its mass as height; the atom guards
    give A_r ≤ 1/k; so t ≤ 1/k < t. Hence i ≠ r.
  - Let Π be the fiber predicate of i for the plateau {r}. A.e. on I_i,
    x ∈ S_P exactly when Π holds.
  - If Π holds, I_i lies a.e. in S_P, and
    `Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.no_cusp_source_peak`
    gives False.
  - If Π fails, a.e. x ∈ I_i is outside S_P, and outside I_r because
    i ≠ r and fibers of distinct atoms are disjoint. Then
    `Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.no_cusp_outside_original_peak`
    gives False.

The two leaves of the template:

- **Peak in the source** (`no_cusp_source_peak`). The source edges of the
  recovered flow have positive mass, the source part of the reverse flow
  has nonnegative energy, and the reverse endpoint lies in a normalized
  range; with the trace cap and the square reserve of the peak these give a
  source budget, and a scalar payment inequality valid for k ≥ 6 fails.
- **Peak outside** (`no_cusp_outside_original_peak`). The square reserve
  of the peak and the full reverse budget give, in normalized masses, an
  inventory, a reserve and a variance inequality together with a positive
  split gap; the scalar gate `Erdos1017.CuspOutsidePeakScalar.outside_contradiction`
  shows these are incompatible for every k ≥ 6, splitting internally into
  k ≥ 9 and k = 6, 7, 8.

### The leaves for each k

| k | root | plateau, height | peak in the source | peak outside |
|---|---|---|---|---|
| k ≥ 6 | `no_cusp_contact_of_six_le` | k ≥ 4 lemmas | `no_cusp_source_peak` | `no_cusp_outside_original_peak` |
| 5, d = 12/25 | `Erdos1017.CappedModel.SelectedHighLowStructure.no_cusp_five_contact` | k ≥ 4 lemmas at k = 5 | `Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.no_cusp_five_source_peak` | `Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.no_cusp_five_outside_original_peak` |
| 4, d = 15/32 | `Erdos1017.CappedModel.SelectedHighLowStructure.no_cusp_four_contact` | k ≥ 4 lemmas at k = 4 | `Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.no_cusp_four_source_peak` | `Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.no_cusp_four_outside_original_peak` |
| 3, ℓ ≥ 1, d = 4/9 | `Erdos1017.CappedModel.SelectedHighLowStructure.no_cusp_three_high_contact` | k = 3 lemmas | `Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.no_cusp_three_high_source_peak` | `Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.no_cusp_three_outside_original_peak` |
| 3, ℓ < 1, d = 4/9 | `Erdos1017.CappedModel.SelectedHighLowStructure.no_cusp_three_low_contact` | not used | see below | see below |

The root `Erdos1017.CappedModel.SelectedHighLowStructure.no_cusp_contact`
splits k ≥ 6 from k ∈ {3, 4, 5} and rewrites d
as 4/9, 15/32 or 12/25. The k = 3 root
`Erdos1017.CappedModel.SelectedHighLowStructure.no_cusp_three_contact`
splits at ℓ = 1. The k = 5, k = 4 and high k = 3 roots repeat the template
with k fixed; their outside leaves have their own scalar sectors, paid by
the reverse endpoint and a peak-avoiding forward endpoint.

### The low-slope third cusp, k = 3 and ℓ < 1

Here a plateau may have two atoms, and the argument looks instead at the
missing region J = Ω ∖ (I_i ∪ N(i)) of the common peak i
(`Erdos1017.CappedModel.SelectedHighLowStructure.cuspThreeMissingRegion`).

- **Universal peak** (`Erdos1017.CappedModel.SelectedHighLowStructure.no_cusp_three_low_slope_universal_peak`).
  The peak has A > 11/39 and 3A² > 2/9
  (`Erdos1017.CappedModel.SelectedHighLowStructure.cusp_three_low_slope_peak_bounds`).
  A universal peak would be NEUTRAL with nonzero body
  (`Erdos1017.CappedModel.SelectedHighLowStructure.no_cusp_three_zero_body`,
  the covered reduction at this cusp), and the universal trace would give
  3A² ≤ 3A² + 2Aγ + γ² ≤ 2h = 2/9 < 3A².
- **Dominant or dispersed** (`Erdos1017.CappedModel.SelectedHighLowStructure.cusp_three_missing_dominant_or_dispersed`).
  For a peak without the universal row, either some atom j ≠ i lies a.e. in
  J with μ(J) − A_j ≤ A_j/20 (it covers at least 20/21 of J), or

      μ(J)²/42 ≤ (1/2)∫∫_{J×J} G.

  The small-missing case is absorbed inside this lemma.
- **Dominant atom** (`Erdos1017.CappedModel.SelectedHighLowStructure.no_cusp_three_dominant_missing_atom`):
  one marked edit pays the remainder J ∖ I_j, and the copy moments of the
  body give the contradiction.
- **Dispersed region** (`Erdos1017.CappedModel.SelectedHighLowStructure.no_cusp_three_dispersed_missing`):
  after the small-missing exit (inside), an edit of the missing region is
  compared with W by global maximality; its density return, the hole
  inventory of the peak and the dispersed edge bound are incompatible with
  the cusp bracket.

---

## 10.6 The W/E₂ corner

`Erdos1017/Exclusions/Corner/SelectedCornerFinalExclusion.lean`, `Erdos1017/Exclusions/Corner/FullSharpCornerPeak.lean`, `Erdos1017/Exclusions/Corner/SelectedCornerRecovery.lean`, `Erdos1017/Exclusions/Corner/SelectedCornerExclusion.lean`, `Erdos1017/Exclusions/Corner/SelectedCornerPositiveSource.lean`, `Erdos1017/Exclusions/Corner/SelectedCornerPrivateExclusion.lean`, `Erdos1017/Exclusions/Corner/SelectedCornerUniversalPrice.lean`, `Erdos1017/Exclusions/Corner/SelectedCornerEmptySource.lean`, `Erdos1017/Certificates/EmptySatCorner/EmptySatCornerMoments.lean`, `Erdos1017/Certificates/EmptySatCorner/EmptySatCornerHardCore.lean`, `Erdos1017/Certificates/EmptySatCorner/EmptySatCornerHardDerivative.lean`, `Erdos1017/Certificates/EmptySatCorner/EmptySatCornerHardLower.lean`, `Erdos1017/Certificates/EmptySatCorner/EmptySatCornerHardMoment.lean`, and 50 further modules under `Erdos1017/Exclusions/Corner/` and `Erdos1017/Certificates/EmptySatCorner/`.

**Setting.** The standing hypotheses hold at the W/E₂ crossing:
ε = 1/2 − d ∈ [ε_C, ε_D] and twoHeadCurve(ε) = mixedCurve(ε). There is no
derivative here; δ = 1 − ℓ throughout this section.

- **Corner parameters** (`Erdos1017.CappedModel.FullStationaryClass.corner_contact_parameters`).
  B is the maximum of the W and E₂ branches and has a kink at the crossing,
  so maximality only places the multiplier between the one-sided slopes of
  the two families (§9); the rational box around the crossing ε_x bounds
  these slopes and the value:

      ℓ ∈ [363/589, 9/11],  c > c_x = 138261458236451/1116960975000000,
      h < h_x = 23243417/10⁸,  γ > 2c_x − ℓh_x.

  So δ ∈ [2/11, 226/589] ⊂ (0, 2/5). The scalar steps below use only these
  guards, plus ε > 1/10 for the plateau bound; the corner gates of the
  zero-body exits use the contact itself, through the block model.
- **Sharp peak** (`Erdos1017.CappedModel.SelectedHighLowStructure.exists_sharp_corner_peak`).
  The common forward peak i has A_i > 1/3, is strictly the largest atom
  and satisfies the square reserve (selector bounds, as in §10.1).
- **One-atom plateau** (`Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.corner_plateau_card_eq_one`).
  Since ℓ > 1/2 and ε ≥ ε_C > 1/10, |P| ≤ 2. A two-atom plateau is
  excluded as in §10.3
  (`Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.no_corner_two_center`):
  the sharp peak lies on the plateau, its body is positive by the corner
  zero-body exclusion (`Erdos1017.CappedModel.SelectedHighLowStructure.no_corner_zero_body`,
  the covered reduction with the corner gates), and the head trace and the
  head budget γ ≤ 2(1 − ℓ)A² contradict the corner parameters.

### Case tree

- **Root** (`Erdos1017.CappedModel.SelectedHighLowStructure.no_corner_global_excess`).
  Take a recovery and split on the compulsory source of its plateau.
  - **Positive source**:
    `Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.no_corner_positive_source`
    (proved in full below).
  - **Null source**: the plateau is {r};
    `Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.no_corner_one_center_empty_source`
    splits on a saturated partner of r.
    - No partner: `Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.no_corner_unsaturated_empty_source`.
      The head is a universal NEUTRAL peak with c ≤ A_r² (§10.0); its body is
      positive (`no_corner_zero_body`); the universal trace, the corner
      parameters and the unsaturated half-quota contradict the scalar
      `Erdos1017.EmptySatCorner.unsaturated_false`.
    - Partner p: `Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.no_corner_saturated_empty_source`,
      the sector table below.

### The saturated null-source sectors

Let (r, p) be saturated, P = {r}, μ(S_P) = 0, A = A_r, b = A_p,
H = H(r, p), U = U(r, p), E = y − A and L = μ(H) + μ(U) − y = 1 − A − b − y.
Call the hole rows *small* if a.e. x ∈ H has missing mass inside H below L
(`Erdos1017.CappedModel.SelectedHighLowStructure.universalPartnerHoleMissingMass`).
The sectors are cut by δ, E and this condition. Two leaves are shared, so
the tree is a directed acyclic graph:

- **Small δ** (`Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.no_corner_saturated_empty_source_small_delta`):
  δ ≤ 21/100.
- **Small excess** (`Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.no_corner_saturated_empty_source_small_excess`):
  L ≤ E.

| hole rows | δ | E | leaf |
|---|---|---|---|
| small | ≤ 1/4 | any | `Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.no_corner_saturated_empty_source_nonexceptional_easy` |
| small | > 1/4 | ≤ 1/20 | the same easy leaf |
| small | > 1/4 | > 1/20 | `Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.no_corner_saturated_empty_source_hard` |
| not small | any | any | `Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.no_corner_saturated_empty_source_exceptional` |

- **Easy sector.** It sends δ ≤ 21/100 to the small-δ leaf and L ≤ E to the
  small-excess leaf. Otherwise the joint signed price `Erdos1017.EmptySatCorner.cornerPrice`
  of the model is negative, while
  `Erdos1017.EmptySatCorner.nonexceptional_easy_price_pos` (with the
  certificates `Erdos1017.EmptySatCorner.small_E_corrected_price_pos` and
  `Erdos1017.EmptySatCorner.middle_delta_corrected_price_pos`, §11) makes it
  positive on δ ∈ [21/100, 2/5], A ∈ [7/20, 3/8] when E ≤ 1/20 or δ ≤ 1/4.
- **Exceptional sector.** A whole atom in H carries missing mass at least
  L. After the same two exits, its degree tangent, stock cap and signed
  restriction price give a raw price that the exceptional certificates
  (`Erdos1017.EmptySatCorner.exceptional_boundary_price_pos`, §11) make
  positive, against the model.
- **Hard sector** (δ > 1/4, E > 1/20). It is the one place where moments
  are needed. After the small-excess exit, let J be the compulsory source
  of the singleton {p} (the partner's source; the source of the plateau
  {r} is null), of mass j. Integrating a rational deficit floor
  δ(L − a) ≤ (L + E − 2a)·w over J, for a mass function a and a deficit
  function w, `Erdos1017.EmptySatCorner.deficit_moment_bounds` gives two
  coupled moments at the mean ā = (∫_J a)/j, together with
  `Erdos1017.EmptySatCorner.mean_mass_bounds_of_deficit_budget`,
  `Erdos1017.EmptySatCorner.triangle_deficit_moment_bound` and
  `Erdos1017.EmptySatCorner.square_moment_triangle_bound`. These place the
  model's data in the range

      0 ≤ ā < E,   (L + E)L ≤ Ej,   2L < j < j_max := 3A − 1 + E + L,

  the upper bound coming from b + j < A. The support intercept, the context
  price and c ≤ A² bound the hard-sector score
  `Erdos1017.EmptySatCornerHard.Phi` of the model by
  Φ(δ, A, E, L, ā, j) ≤ 0 (Lean's q is ā); the guard
  `Erdos1017.EmptySatCornerHard.selector_guard_pos` enters this cost bound.
  On the other side, Φ > 0 whenever δ ∈ [1/4, 2/5], A ∈ [7/20, 3/8],
  E ∈ [1/20, 29/250], L ∈ [E, E + (3A − 1)/2], ā ∈ [0, E] and
  j ∈ [(L + E)L/E, j_max]. The model satisfies these, since
  (L + E)L ≤ Ej gives the lower bound on j. The proof combines three charts:
  - at ā = 0 the j-derivative of Φ is positive on all of [2L, j_max]
    (`Erdos1017.EmptySatCornerHard.zero_derivative_pos`, from the Bernstein
    chart `Erdos1017.EmptySatCornerHard.derivative_chart`);
  - at ā = 0 and j = (L + E)L/E, Φ is positive
    (`Erdos1017.EmptySatCornerHard.zero_lower_endpoint_pos`, from
    `Erdos1017.EmptySatCornerHard.lower_chart`); this endpoint lies in
    [2L, j_max] because L ≥ E, so by monotonicity Φ > 0 at ā = 0 for
    every j ∈ [(L + E)L/E, j_max];
  - at ā = E, Φ is positive on all of [2L, j_max]
    (`Erdos1017.EmptySatCornerHard.moment_endpoint_pos`, from
    `Erdos1017.EmptySatCornerHard.moment_chart`);
  - positivity at the two moment endpoints ā = 0 and ā = E gives Φ > 0 for
    ā ∈ [0, E].

  Positivity at ā = 0 is not claimed on [2L, (L + E)L/E); the model's j
  never lies there. The prism is wider than the corner requires
  (δ ≤ 226/589 < 2/5). The chart mechanics are in `certificates.md`.

### The positive-source leaf, proved in full

- **Positive source** (`Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.no_corner_positive_source`, `Erdos1017/Exclusions/Corner/SelectedCornerExclusion.lean`).
  Under the standing hypotheses at the corner, a recovery whose compulsory
  source has positive measure is impossible.
  - The plateau has one atom (`corner_plateau_card_eq_one`).
  - Let r be the sharp common peak (`exists_sharp_corner_peak`).
  - `Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.exists_corner_one_center_saturated_universal`,
    applied to the one-atom plateau, the positive source and the common
    peak r, gives an atom p with P = {p}, r ≠ p, (r, p) saturated and r
    universal. Inside it, the private alternative is closed by
    `Erdos1017.CappedModel.SelectedHighLowStructure.no_corner_private_common_peak`
    (the slope, physical exposure, private covariance and both partner-star
    cases at the corner).
  - `Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery.no_corner_one_center_universal`,
    applied to P = {p}, the saturated pair (r, p), the common peak r and its
    universal row, gives False.

The last step reruns, at the corner, the universal saturated price
argument of §10.3: it uses the same objects (the universal physical primal
at r, the negative region of U(r, p), the shared-hole radius and the copy
error of the partner row), with the corner parameters in place of the
upper E₂ scalars.
