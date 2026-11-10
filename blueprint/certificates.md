# Blueprint: the computer-checked certificates

This document holds §11 of the blueprint (sections 11.1 to 11.5); `proof.md`
holds the statement, §0 to §7 and §9. Like the rest of the blueprint it
gives its part of the argument in prose, following the Lean development
module by module and naming the modules and declarations of each section,
with the conventions, notation and credits of `proof.md`. It states what
each certificate proves over the reals, how its arithmetic is checked, and
which exclusion of §10 (`exclusions.md`) uses it. Every certificate is a
Lean theorem checked by the kernel; no external computation is trusted.
Certificate variables are defined where they occur; where a Lean name
clashes with the notation of `proof.md` §0, the variable is renamed and the
Lean name is given.

---

## 11.1 The certificate contract

The 168 modules of §11 are: the large universal-head cover, 156 modules of
`Erdos1017/Certificates/MiddleE2LargeUniversal/` (the eight listed in §11.2 and 148
generated pieces; the folder's two other modules belong to §10.4); the corner
certificates `Erdos1017/Certificates/EmptySatCorner/EmptySatCornerCertificates.lean` and
`Erdos1017/Certificates/EmptySatCorner/EmptySatCornerHardCertificates.lean` (the other
34 modules of that folder belong to §10.6); and the ten small modules of
§11.4, which sit in the folders of the sections that use them. A certificate
is a Lean theorem proved by an exact check of explicit finite data, in one of
three ways.

- **A kernel-evaluated cover** (§11.2). A Boolean function `cover` on integer
  data; a soundness theorem, proved for all inputs by reasoning over the
  reals, that `cover … = true` implies the wanted real inequalities; and the
  Boolean fact, assembled from `decide +kernel` proofs of `coverC … = true`,
  where `coverC` follows a literal certificate tree, and a theorem deriving
  `cover` from `coverC`. Each such proof is accepted only if the kernel itself
  reduces `coverC …` to `true` by definitional unfolding, with its built-in
  arithmetic on natural-number literals, to which the integer operations
  unfold; neither the elaborator nor compiled code evaluates
  anything. Each Boolean value is thus a theorem of the kernel. The soundness
  theorems never evaluate `cover` or a leaf test; the only numerals they check
  are the scale and the window endpoints.
- **Bernstein certificates** (§11.3, part of §11.4). Each coordinate is mapped
  affinely onto [0, 1], with endpoints that may depend on the earlier
  coordinates. An identity proved by `norm_num [bernstein_apply]` and `ring`
  writes a positive constant times the target polynomial (minus the bound,
  for a chart proving a lower bound) as Σ c_α B_α, where B_α is a product of
  Mathlib's Bernstein polynomials `bernstein n i` and the c_α are explicit
  rationals. The B_α are nonnegative with sum 1 on the cube, so c_α ≥ c for
  all α gives a value at least c; the bounds c_α ≥ c are checked by
  `norm_num`, or hold by construction (§11.3).
- **Closed-form inequalities** (§11.4): `nlinarith`, `positivity`,
  `field_simp` and `ring` with rational constants, and one counting argument.

`decide +kernel` occurs only in the 148 pieces, 11,882 times; `native_decide`,
`sorry` and axiom declarations occur nowhere in `Erdos1017/`. Programs outside
the library only write Lean source (§11.5). The consumers are §10.4 (branch
U) for the cover, whose premise §1 discharges; §10.6 (the null-source
saturated corner) for the corner certificates; and §2, §6, §7, §10.0 and
§10.2 to §10.5 for the small certificates (table of §11.4).

---

## 11.2 The large universal-head cover

`Erdos1017/Certificates/MiddleE2LargeUniversal/MiddleE2LargeUniversalFixedPoint.lean`,
`Erdos1017/Certificates/MiddleE2LargeUniversal/MiddleE2LargeUniversalCertificateChecker.lean`,
`Erdos1017/Certificates/MiddleE2LargeUniversal/MiddleE2LargeUniversalCertificatePartition.lean`,
`Erdos1017/Certificates/MiddleE2LargeUniversal/MiddleE2LargeUniversalCertificateContraction.lean`,
`Erdos1017/Certificates/MiddleE2LargeUniversal/MiddleE2LargeUniversalCertificateSound.lean`,
`Erdos1017/Certificates/MiddleE2LargeUniversal/MiddleE2LargeUniversalCertificateKernelChecker.lean`,
`Erdos1017/Certificates/MiddleE2LargeUniversal/MiddleE2LargeUniversalCertificateCover.lean`,
`Erdos1017/Certificates/MiddleE2LargeUniversal/MiddleE2LargeUniversalCertificateRoot.lean`, and the 148 pieces
`Erdos1017/Certificates/MiddleE2LargeUniversal/MiddleE2LargeUniversalCertificatePiece000.lean` to
`Erdos1017/Certificates/MiddleE2LargeUniversal/MiddleE2LargeUniversalCertificatePiece147.lean`. The statement certified is
defined in the §10.4 modules `Erdos1017/Certificates/MiddleE2LargeUniversal/MiddleE2LargeUniversalParams.lean` and
`Erdos1017/Certificates/MiddleE2LargeUniversal/MiddleE2LargeUniversalContract.lean`.

**The statement certified.** Branch U of
`Erdos1017.CappedModel.SelectedHighLowStructure.no_middle_e2_contact_of_cover`
(§10.4) reads off the model the point P = (q, A, b, u) of
`Erdos1017.CappedModel.SelectedHighLowStructure.middleLargeUniversalPoint`
(the E₂ parameter, the masses of the universal head and of its saturated
partner, the measure of the common region), proves that P lies in the window
and satisfies the necessary inequalities below, and needs the price tests. A
`Erdos1017.MiddleE2LargeUniversal.Point` has the four fields q, A, b, u. With
R(q) = 1 + 7q + q², ℓ(q), g(q), h(q) of `proof.md` §0 and δ(q) = 1 − ℓ(q), the
certificate uses

    y*(q) = 9q/(2R(q)) = 1 − 2g(q)/δ(q)   (Lean's `y`, the bound on the deficit ratio y),
    K(q) = 9q²(1 − q²)/(4R(q)²)           (the forward-gap constant),

and 23 further definitions of the namespace `Point`, built by +, −, ×, ÷, min,
max, one case split and one square root. Among them are e = 1 − A − b − u
(Lean's `eta`), RP = ℓ(1 − A) − A + g, v₀ = 1 − 2h − u (Lean's `v`),
p = y* − u, the additional-hole error E₀ (Lean's `E`) and the signed price
(Lean's `G`)

    G₀ = max(0, bℓ − g)·e/pole + ℓ(RC − A + b) − g + E₀;

sc, C, Q, lpf, joint, RC, pole, moment and zeroprice are defined in
`Erdos1017/Certificates/MiddleE2LargeUniversal/MiddleE2LargeUniversalContract.lean`.
`Erdos1017.MiddleE2LargeUniversal.Point.InBox` is q ∈ [157/1000, 1/5],
A ∈ [1/3, 369/1000], b, u ∈ [0, 1/3];
`Erdos1017.MiddleE2LargeUniversal.Point.Necessary` is the sixteen
inequalities (r0 = 1 − 2A)

    A ≤ y*, 3A − 1 ≤ b ≤ r0, b ≤ A − K, RP ≤ 2ℓu, u ≤ r0, u ≤ 1 − 2ℓA − 3g,
    e, RC, sc, C, Q ≥ 0, min(e/2, e − C) ≤ p, v₀ > 0, lpf ≤ p, joint ≤ 0;

`Erdos1017.MiddleE2LargeUniversal.Point.PriceTests` is pole > 0, u > 0,
RP > 0, moment > 0, zeroprice > 0, g − E₀ > 0 and G₀ < 0.

**Fixed-point intervals** (`Erdos1017.MiddleE2LargeUniversal.FixedPoint.S`,
`Erdos1017.MiddleE2LargeUniversal.FixedPoint.FI`,
`Erdos1017.MiddleE2LargeUniversal.FixedPoint.SMem`). The scale is
S₀ = 1000·2³⁰ = 1,073,741,824,000 (Lean's `S`); an `FI` is an integer pair
(lo, hi), and `SMem x a` means lo ≤ x·S₀ ≤ hi. Sums and differences are
exact; a product takes ⌊min/S₀⌋ and ⌈max/S₀⌉ of the corner products; a
reciprocal (⌊S₀²/hi⌋, ⌈S₀²/lo⌉) follows a positive lower endpoint. Rounding
is outward, by integer division, with no rational normalization. The square
root keeps a candidate l from an untrusted Newton iteration only if l² ≤ lo·S₀
(else 0), and h only if hi·S₀ ≤ h² (else max(S₀, hi)). Each operation has an
enclosure lemma, such as `Erdos1017.MiddleE2LargeUniversal.FixedPoint.mem_fsqrt`:
values in the argument intervals (and a positive divisor lower endpoint) give
a value in the result interval.

**Boxes** (`Erdos1017.MiddleE2LargeUniversal.FixedPoint.IBox`,
`Erdos1017.MiddleE2LargeUniversal.FixedPoint.IBox.split`). An `IBox` stores
(i_c, k_c) for c = q, A, b, u; coordinate c ranges over the scaled segment
[o_c + ⌊w_c i_c/2^(k_c)⌋, o_c + ⌊w_c(i_c + 1)/2^(k_c)⌋], with (o, w) equal to
(157·2³⁰, 43·2³⁰) for q, (⌊S₀/3⌋, 369·2³⁰ − ⌊S₀/3⌋) for A and (0, ⌈S₀/3⌉)
for b and u. `IBox.split` bisects a coordinate of least k_c (ties in the order
q, A, b, u), (i, k) becoming (2i, k + 1) and (2i + 1, k + 1). The root
`Erdos1017.MiddleE2LargeUniversal.FixedPoint.IBox.root` is
`IBox.mk 0 0 0 0 0 0 0 0`.

**The leaf test** (`Erdos1017.MiddleE2LargeUniversal.FixedPoint.leafOK`,
`Erdos1017.MiddleE2LargeUniversal.FixedPoint.necFail`,
`Erdos1017.MiddleE2LargeUniversal.FixedPoint.priceOK`). The parameters are
enclosed from their values at the two q endpoints of the box, by monotonicity
on [157/1000, 1/5]: ℓ decreases and g, y* increase; h = f₁²(1 + 4q + 13q²)/8
and K = (9/4)f₂²(1 − q²) are enclosed as products of the monotone factors
f₁ = (q + 2)/R(q) (decreasing), f₂ = q/R(q) and 1 + 4q + 13q² (increasing);
RP and the selector surplus are monotone in q and A. These lemmas are proved
over the reals by `nlinarith` or `linarith` in
`Erdos1017/Certificates/MiddleE2LargeUniversal/MiddleE2LargeUniversalParams.lean`. `leafOK B` needs positive enclosures of
2 + q, 2R(q), R(q) at both endpoints and of ℓ. It contracts twice (A below y*,
(1 + b)/3, (1 − b)/2; b into [3A − 1, min(r0, A − K)]; u into
[RP/(2ℓ), min(r0, 1 − 2ℓA − 3g)]; each bound is a `Necessary` inequality) and
succeeds if an interval empties or, with ℓ and 1/5 − δ enclosed positive, if
`necFail` (an enclosure of one of 13 necessary quantities has the wrong sign)
or `priceOK` (lower endpoints of pole, u, RP, A, the denominator of E₀,
moment, zeroprice and g − E₀ positive, upper endpoint of G₀ negative) holds.
Then `Erdos1017.MiddleE2LargeUniversal.FixedPoint.cover` is

    cover 0 B = leafOK B,   cover (n + 1) B = leafOK B || (cover n B.split.1 && cover n B.split.2).

**Soundness.** B contains P if each coordinate of P lies in its segment, and B
is valid if i_c < 2^(k_c) for each c.

- **Partition** (`Erdos1017.MiddleE2LargeUniversal.FixedPoint.IBox.split_cover`,
  `Erdos1017.MiddleE2LargeUniversal.FixedPoint.IBox.root_contains`). If B
  contains P, a child of B contains P; the root, which is valid, contains
  every `InBox` point; validity passes to children.
  - As ⌊2wi/2^(k+1)⌋ = ⌊wi/2^k⌋ and ⌊2w(i + 1)/2^(k+1)⌋ = ⌊w(i + 1)/2^k⌋,
    the children keep the parent's outer endpoints and share
    ⌊w(2i + 1)/2^(k+1)⌋, whatever the rounding. The root's endpoints are the
    integers above, rounded outward.
- **Leaf soundness**
  (`Erdos1017.MiddleE2LargeUniversal.FixedPoint.leafOK_sound`). If B is valid
  and contains P, P is `InBox` and `Necessary`, and leafOK B = true, then P
  satisfies `PriceTests`.
  - Validity keeps B in the window, so the endpoint values and monotonicity
    enclose P's parameters. Contraction keeps P
    (`Erdos1017.MiddleE2LargeUniversal.FixedPoint.cA_sound`,
    `Erdos1017.MiddleE2LargeUniversal.FixedPoint.cb_sound`,
    `Erdos1017.MiddleE2LargeUniversal.FixedPoint.cu_sound`), so no interval
    empties. Every tested quantity is computed from these enclosures by
    operations with enclosure lemmas, whose positive-divisor conditions are
    among the tests, so its interval contains P's value. A `necFail` test
    would contradict a `Necessary` inequality of P, so `priceOK` holds, and
    its endpoints give `PriceTests`.
- **Cover soundness and the interface**
  (`Erdos1017.MiddleE2LargeUniversal.FixedPoint.cover_sound`,
  `Erdos1017.MiddleE2LargeUniversal.FixedPoint.priceTests_of_cover`). If P is
  `InBox` and `Necessary`, then for all n and all valid B containing P,
  cover n B = true implies `PriceTests` P; so cover 80 IBox.root = true gives
  `PriceTests` for every `InBox`, `Necessary` P.
  - Induction on n: at 0, leaf soundness; at n + 1, either leafOK B = true, or
    both children are covered at depth n and one of them, valid, contains P.
    The interface applies this at the root.

**Certificate trees** (`Erdos1017.MiddleE2LargeUniversal.FixedPoint.Cert`,
`Erdos1017.MiddleE2LargeUniversal.FixedPoint.coverC`,
`Erdos1017.MiddleE2LargeUniversal.FixedPoint.coverC_sound`,
`Erdos1017.MiddleE2LargeUniversal.FixedPoint.Kernel.leafOK`,
`Erdos1017.MiddleE2LargeUniversal.FixedPoint.Kernel.leafOK_eq`). A `Cert` is
the shape of a binary tree, and `coverC` follows a given shape c, with the
depth n as fuel:

    coverC .leaf n B = Kernel.leafOK B,   coverC (.node l r) 0 B = false,
    coverC (.node l r) (n + 1) B = coverC l n B.split.1 && coverC r n B.split.2.

So the leaf test runs only at the leaves of c, and every other box is split.
`Kernel.leafOK` is the leaf test written for the kernel: integer addition,
subtraction, multiplication, division and comparison match on the
constructors `Int.ofNat` and `Int.negSucc` and apply the natural-number
operations directly, so the kernel does not unfold the instances behind
them, and every other definition is copied on these operations.
`Kernel.leafOK_eq` proves Kernel.leafOK B = leafOK B for every B, one
definition at a time, with no range assumptions. `coverC_sound` turns
coverC c n B = true into cover n B = true by induction on c, with
`Kernel.leafOK_eq` at the leaves and `cover_of_split` at the nodes.

**The computation**
(`Erdos1017.MiddleE2LargeUniversal.FixedPoint.cover_of_split`,
`Erdos1017.MiddleE2LargeUniversal.FixedPoint.Cov.t0`,
`Erdos1017.MiddleE2LargeUniversal.FixedPoint.cover_root`). A script matching
`theorem tN : cover d (IBox.mk …) = true` over the pieces and the root module
counts 23,763 theorems `Cov.t0` to `Cov.t23762` (23,616 in the pieces, 147 in
the root), each with d + k_q + k_A + k_b + k_u = 80. The boxes that the
evaluation of cover 80 IBox.root visits form the search tree, of 291,647
boxes: 145,824 pass the leaf test and 145,823 are split.

- 11,882 leaves, all in the pieces, are proved by `decide +kernel`, on boxes
  of dyadic depth 4 to 28, so with budgets d from 52 to 76 (8,058 from 57 to
  62). The leaf for B at budget d is coverC_sound applied to a
  `decide +kernel` proof of coverC c d B = true, where c is the literal shape
  of the search tree below B, of at most 40 boxes (§11.5). The kernel thus
  runs the leaf test only at the 145,824 boxes that pass it. `Cov.t0` is
  cover 72 (IBox.mk 0 2 0 2 0 2 0 2) = true.
- The other 11,881 (11,734 in the pieces, 147 in the root) are
  `cover_of_split t_i t_j`; `cover_of_split` turns cover n B.split.1 = true
  and cover n B.split.2 = true into cover (n + 1) B = true by rewriting, and
  the application type-checks only if t_i, t_j state the two halves of the
  explicit B, which Lean confirms by unfolding `IBox.split`.
- `cover_root` is `Erdos1017.MiddleE2LargeUniversal.FixedPoint.Cov.t23762`,
  that is cover 80 (IBox.mk 0 0 0 0 0 0 0 0) = true, built from `t9436` and
  `t23761`; `Erdos1017/FinalAssembly.lean` passes it to
  `Erdos1017.densityLimit_le_benchmark_of_cover`.

---

## 11.3 The corner certificates

`Erdos1017/Certificates/EmptySatCorner/EmptySatCornerCertificates.lean`,
`Erdos1017/Certificates/EmptySatCorner/EmptySatCornerHardCertificates.lean`.

Both serve the null-source saturated corner of §10.6 and use its variables:
δ = 1 − ℓ, the head mass A, the partner mass b, the deficit ratio y, the
excess E = y − A, L = 1 − A − b − y and the source mass j. They are
positivity statements over the reals, consumed by `EmptySatCornerScalar` and
`SelectedCornerEmptySource` (§10.6).

- **The joint price** (`Erdos1017.EmptySatCorner.cornerPrice`). With
  v = 2A − 1 + y, K_v = (2 − δ)v − y/12, σ = (4(2 − δ)v + 8y)/25,
  γ = δ(1 − y)/2 and U* = 1 − 2(1 − δ)A − 3γ,

        cornerPrice(δ, A, E, L) = 37/1250 − 2(1 − δ)v² − y²/12 + (12/25)K_v²
                                   − σL − (8/25)L² + 4δ(1 − A − y − L)(y − U*).

  Let cap(δ) = 336/625 − 37/(1250δ) and τ(δ, A) = 467/1000 − 3A² − 2Aγ₀ − γ₀²,
  γ₀ = (23/100)δ + 37/2500.
- **Joint and corrected prices.** For δ ∈ [21/100, 2/5], A ∈ [7/20, 3/8]:
  cornerPrice(δ, A, E, E) > 0 if 0 ≤ E ≤ cap(δ) − A
  (`Erdos1017.EmptySatCorner.small_L_price_pos`), and
  cornerPrice − (cap(δ) − y)/25 − τ/6 > 0 if E ∈ [0, 1/20], L ∈ [E, 1/10]
  (`Erdos1017.EmptySatCorner.small_E_corrected_price_pos`). For
  δ ∈ [37/172, 1/4], A ∈ [7/20, cap(δ) − 1/20], E ∈ [1/20, cap(δ) − A],
  L ∈ [E, E + (3A − 1)/2]: cornerPrice − τ/6 > 0
  (`Erdos1017.EmptySatCorner.middle_delta_corrected_price_pos`).
- **Exceptional sector.** For δ ∈ [21/100, 2/5], A ∈ [3507/10000, 3/8],
  E ∈ [0, cap(δ) − A] and θ ∈ [0, (2 − 5A − 2E)/6] (Lean's `r`), the
  exceptional price `Erdos1017.EmptySatCorner.cornerExceptionalPrice` at
  (δ, A, E, E + 6θ, θ) is positive
  (`Erdos1017.EmptySatCorner.exceptional_boundary_price_pos`), and five
  rational guards hold (`Erdos1017.EmptySatCorner.exceptional_guards`).
- **Small δ.** For δ ∈ [2/11, 21/100], with the scores
  `Erdos1017.EmptySatE2.baseScore`, `Erdos1017.EmptySatE2.supportScore` and
  `Erdos1017.EmptySatE2.exceptionalBaseScore` of §10.0 taken at h = 467/2000:
  - if y ∈ [7/20, 27/50 − 37/(1250δ)], the support score at A = 7/20 is
    positive (`Erdos1017.EmptySatCorner.small_delta_support_endpoint_pos`),
    and the exceptional score is positive at A = 7/20 and at A = y
    (`Erdos1017.EmptySatCorner.small_delta_exceptional_endpoints_pos`);
  - if y ∈ [7/20, 2/5], E ∈ [0, y − 7/20] and A = y − E, the radical endpoint
    X₀ = baseScore(δ, h, A, y) + 4δy(1 − A − y) − (8/25)yE is positive and
    (σ + 4δy)²yE < X₀² (`Erdos1017.EmptySatCorner.small_delta_radical_separation`).
- **Mechanism.** Each coordinate is a + (b′ − a)t with t ∈ [0, 1], the
  endpoints depending on earlier coordinates; widths such as cap(δ) − A are
  cleared by a factor δ, since δ·cap(δ) is a polynomial. Fifteen charts give
  an integer denominator and integer coefficients with
  denominator × polynomial = Σ c_α B_α; thirteen have all c_α ≥ 1 (checked by
  `fin_cases` and `norm_num`), and two have c_α ≥ 0 and prove the lower
  bounds 4669/50000 and 7067/25000 of `exceptional_guards`. There are 691
  coefficients, 135 for each of the middle and exceptional prices.
- **Hard sector** (`Erdos1017.EmptySatCornerHard.zero_derivative_pos`,
  `Erdos1017.EmptySatCornerHard.moment_endpoint_pos`). On δ ∈ [1/4, 2/5],
  A ∈ [7/20, 3/8], E ∈ [1/20, 29/250], L ∈ [E, E + (3A − 1)/2],
  j ∈ [2L, 3A + E − 1 + L], the j-derivative of the zero-moment score is
  positive and the score `Erdos1017.EmptySatCornerHard.Phi` is positive at
  moment coordinate E; companions give Φ > 0 at moment 0, j = (L + E)L/E, and
  a selector guard in (δ, A, E).
  - Each maps its five, four or three coordinates onto a unit cube, clears
    positive factors and applies a chart of §10.6, such as
    `Erdos1017.EmptySatCornerHard.derivative_chart`; the four tables have
    4·5·5·4·4 = 1,600, 4·7·7·6·5 = 5,880, 4·10·10·9 = 3,600 and
    2·4·3 = 24 entries, each stored as a natural number N − 1, so N ≥ 1 by
    construction. The guard chart is one Bernstein identity. The others go by
    stages, each evaluating the previous one in one more coordinate: stage-1
    rows by `Erdos1017.EmptySatCornerHard.bEval_nat_power` (Bernstein to power
    basis), later rows by `norm_num [bernstein_apply]` and `ring`;
    `Erdos1017.EmptySatCornerHard.bEval_one_le` carries the bound 1 to the
    last stage, the denominator times the target.

---

## 11.4 Small scalar certificates

`Erdos1017/Exclusions/E2/Lower/LowerE2ScalarCertificates.lean`,
`Erdos1017/Exclusions/E2/Upper/UpperE2UniversalBoundaryCertificates.lean`,
`Erdos1017/Multipartite/TwoHead/TwoHeadFamilyCertificates.lean`,
`Erdos1017/Exclusions/Cusp/CuspOutsideHoleCertificates.lean`,
`Erdos1017/Exclusions/Cusp/CuspOutsideSmallRangeCertificates.lean`,
`Erdos1017/Exclusions/Cusp/CuspOutsideLargeCertificates.lean`,
`Erdos1017/Exclusions/Common/E2/E2PrivateCurvatureCertificates.lean`,
`Erdos1017/Exclusions/Common/E2/EmptySatE2Certificates.lean`,
`Erdos1017/Models/PhysicalPrimal/FiniteHubCertificate.lean`,
`Erdos1017/Exclusions/Common/SharpCounts/SharpSelectorTripleCertificate.lean`.

None uses `decide`. R(q) = 1 + 7q + q²; consumers are named by section and
module.

| Family | Real statement | Variables and domain | Arithmetic | Mechanism | Consumer |
|---|---|---|---|---|---|
| E₂ scalars, `Erdos1017.LowerE2Scalar.multiplier` | defines ℓ(q) = (2 − q)/(2 + q), h(q), g(q) and the pair floor; h(q) = 2·twoHeadDensity((q + 2)/3) (`Erdos1017.LowerE2Scalar.missingMass_eq_twoHeadDensity`); g(q) = 2·twoHeadValue((q + 2)/3) − ℓ(q)h(q) (`Erdos1017.LowerE2Scalar.gapFloor_eq_twoHeadValue`); pair floor > 0 (`Erdos1017.LowerE2Scalar.pairFloor_pos`); 9q/(2R(q)) < 2/7 (`Erdos1017.LowerE2Scalar.ratio_lt_two_sevenths`) | q ≥ 0; q ∈ [0, 1/10]; q ∈ [0, 1/9] | exact rational identities, polynomial bounds | `field_simp`, `ring`; `gcongr`, `nlinarith` | §2, §10.0, §10.2, §10.3, §10.4 |
| Upper E₂ boundary, `Erdos1017.UpperE2UniversalScalar.enlargedF_neg` | the enlarged signed price of §10.3 is negative; its pole exceeds 1/200 (`Erdos1017.UpperE2UniversalScalar.enlarged_pole_pos`) | b ∈ [77/1098, 1/4], 0 ≤ z ≤ b, 1547/4026 − b + 4z/5 ≤ e ≤ 2/3 − b − z (Lean's `eta`), moment cap ≥ 0 | rational tensor Bernstein coefficients on (b, z) rectangles | two-kink piecewise argument in e, leaving four endpoint families; 16 charts; `norm_num`, `nlinarith` | §10.3, `UpperE2UniversalReduction` |
| Two-head branch, `Erdos1017.TwoHeadFamilyCertificates.branchValue_lt_splitLower` | (10x + (6 − 4x)s − s²)/12 < (1 + x²)(1 − √(1 + x²)/(1 + x + s)) | s ∈ [1, 5/3] (Lean's `S`), x ∈ [0, 1] | four 20-coefficient rational tensor Bernstein rectangles, lower bounds 23/54, 5/8, 17/108, 299/216 | Bernstein lower bound; `field_simp`; √(1 + x²) ≤ 1 + x²/2 | §7, `TwoHeadTailComparison` |
| Cusp holes and cells, `Erdos1017.CuspOutsideHole.outside_six_contradiction` | no (p, t, X, Z) with 1 ≤ X + 2pt − 2p² + Z, p² ≤ X, t² + Z ≤ 11/5, X ≤ 24/1015, Z ≤ 18/35 (also k = 7, 8); one-variable cell and envelope bounds such as (−107x² + 336x − 264)/84 < 0 (`Erdos1017.CuspOutsideSmallRange.six_cell_three_neg`) | reals; X is Lean's `W` | rational constants | weighted-square identity (`Erdos1017.CuspOutsideHole.weighted_inventory_bound`, weights 8, 9, 11); completed squares; `nlinarith` | §10.5, `CuspOutsideSmallExclusion`, `CuspOutsideSmallCaps` |
| Large cusps, `Erdos1017.CuspOutsideLarge.outside_large_excess_neg` | x²(Δ − 19x/20) < Δ − 1 | k ≥ 9 real (Lean's `m`), Δ ≤ (2k + 1)/(k + 1) (Lean's `D`), x ≥ 0, x² ≥ k(k + 3)/(2(2k + 1)) | polynomial in k − 9 with positive coefficients | cubic monotonicity, `nlinarith` | §10.5, `CuspOutsideLargeSplitGap` |
| E₂ curvature, `Erdos1017.E2PrivateCurvature.curvature_pos_lt_six` | 0 < κ(q) < 6, κ(q) = 32R(q)³/(9(q + 2)³(1 − 3q² − 7q³)) | q ∈ [0, 1/5] | degree-six margin polynomial, 27926/3125 at q = 1/5 | clearing identity by `ring`; monotonicity by `gcongr` | §10.0, `FullE2ContactCurvature`; §10.4 private sector |
| Empty-source E₂ scores, `Erdos1017.EmptySatE2.support_numerator_pos` | support score positive at A = 7/20; exceptional score positive at A = 7/20 and A = y (`Erdos1017.EmptySatE2.supportScore_lower_pos`, `Erdos1017.EmptySatE2.exceptionalBaseScore_endpoints_pos`) | q ∈ [9/50, 213/1000], y ∈ [7/20, 19/50] (Lean's `D`) | three 21-coefficient rational tensor Bernstein certificates | Bernstein positivity; clearing by `field_simp`, `ring` | §10.0, `EmptySatE2Scalar`; thence §10.4, §10.6 |
| Finite hub, `Erdos1017.FiniteArity.omitted_clique_negative` | the pair charge of U is negative | finite U of more than `N` points, charges in [−3, 1] with zero diagonal; explicit naturals `h`, `k`, `B`, `T`, `C`, `N` (Lean's names) with the size and cutoff conditions; subsets of at most `N` points have pair charge ≤ 1; the hub tests of order `k` pass | integer counting | signature bins; `omega`, `linarith`; no numerics | §6, `FiniteArityParameters` |
| Sharp selector, `Erdos1017.Selector.Sharp.centered_intercept_le_one` | Λ ≤ 1 (Lean's `L`) | p_i ∈ [0, 1], Σ p_i = 2, K symmetric, Σ_j p_j K_ij = 0, K_ii ≥ 0 if p_i > 0, 3Λ − 3 − 2(K_ij + K_ik + K_jk) ≤ 0 on occupied distinct triples, one such triple | exact identity | weighted triple sum = (3Λ − 3)·(triple mass) + 12 Σ p_i²(1 − p_i)K_ii (`Erdos1017.Selector.Sharp.tripleSum_centered_identity`); `nlinarith` | §10.0, `SharpSelectorSumTwo` |

---

## 11.5 Generators and reproducibility

No modules. The generators are in `scripts/`, which no library target of
`lakefile.toml` includes and no proof imports. They are not trusted: the
kernel checks the certificates directly, and a faulty generator can at worst
write a statement that fails to check. The Python scripts use only the
standard library.

- **The large cover.** `lake env lean
  scripts/MiddleE2LargeUniversalCertificateCoverGen.lean`, on a built
  library, evaluates `leafOK` with `#eval` to build the search tree of
  `cover 80 IBox.root` (names as in §11.2). Each subtree of more than 40 boxes
  becomes a `cover_of_split` theorem and each other subtree a `decide +kernel`
  leaf on the `Cert` literal of its shape, so the kernel visits at most 40
  boxes inside a leaf (a bound no proof uses); the theorems go in post-order
  to `.lake/cover-shards/`. On the committed tree it takes about six
  minutes and about 1.1 GB of memory and writes 10 shards.
  `python3 scripts/split_cover_certificate.py [--shards DIR]
  [output-directory]` (shards default to `.lake/cover-shards/`) checks that
  the declarations form one tree in post-order, every `cover_of_split`
  referring to an earlier theorem, and cuts it into maximal subtrees of at
  most 150 leaves (the 148 pieces) and the 147 nodes above them (the root
  module); otherwise it exits with an error and writes nothing. It writes the
  149 files to an output directory, by default `.lake/cover-certificate/`,
  never into the library; with `--check` it compares them byte for byte with
  the library, printing `23763 declarations: 148 pieces, 147 root nodes`
  and `149 of 149 modules identical` in under a second. Run on the
  shards that the search program writes, the check reports all 149 modules
  identical, so the search program and the splitter together reproduce the
  committed cover byte for byte.
- **The hard corner.** `scripts/corner_certificate/hard.py` is the
  exact checker of the hard sector: it expands four polynomials in the
  Bernstein basis in rational arithmetic and asserts that all 11,104
  coefficients are positive.
  `python3 scripts/corner_certificate/generate_hard_corner.py` checks the
  SHA-256 digest of `hard.py`, runs it, compares the coefficient digests with
  the digests recorded in the generator, scales each table to positive integers
  and writes the 32 modules `EmptySatCornerHard*.lean` (the §11.3 wrapper and
  the 31 chart modules of §10.6) to an output directory, by default
  `.lake/hard-corner-certificate/`, never into the library. With `--check` it
  writes nothing, compares the 32 modules byte for byte with the library
  (printing `differs:` or `not generated:` for any mismatch), prints "32 of 32
  modules identical" and exits 0, in one to two seconds; it needs Python 3.9 or
  later. The hand-written Lean of these modules (score formulas, chart-identity
  templates) is embedded verbatim in the script, so byte equality checks the
  tables and the layout, not an independent derivation of the formulas.
- The other certificate data (`Erdos1017/Certificates/EmptySatCorner/EmptySatCornerCertificates.lean` and §11.4) are
  written directly in the Lean files.
