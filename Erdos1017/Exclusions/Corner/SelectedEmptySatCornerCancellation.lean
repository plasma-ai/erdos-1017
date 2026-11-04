module

public import Erdos1017.Exclusions.Corner.SelectedEmptySatCornerContext
public import Erdos1017.Exclusions.Corner.SelectedEmptySatCornerQuota
public import Erdos1017.Exclusions.Corner.SelectedEmptySatCornerSourceGeometry

/-!
# Private-source selector refund at the empty-source saturated corner

This module defines the edge mass, signed charge and selector refund inside the
partner-private source, shows the private-source budget pays both selector
denominators and the refund, and that deleted original subcliques give a
nonnegative slack, so the selector sums measurable signed functions of each
parent.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ}

/-- Actual unordered graph mass inside the entire partner-private source. -/
def emptySatPrivateEdgeMass (S : SelectedHighLowStructure W m) (p : S.I) : ℝ :=
  (∫ z, PhysicalCliqueRepresentative.edgeIndicator
    (Function.uncurry (PhysicalRepresentative.adjacency W m)) z
      ∂(μ.restrict (S.reverseCompulsorySource {p})).prod
        (μ.restrict (S.reverseCompulsorySource {p}))) / 2

/-- Signed unordered charge inside the entire original private source. -/
def emptySatPrivateCharge (S : SelectedHighLowStructure W m) (p : S.I) : ℝ :=
  (∫ z, PhysicalRepresentative.charge W m z.1 z.2
    ∂(μ.restrict (S.reverseCompulsorySource {p})).prod
      (μ.restrict (S.reverseCompulsorySource {p}))) / 2

/-- The exact nonempty source-selector refund on the original source law. -/
def emptySatPrivateSelectorRefund (S : SelectedHighLowStructure W m) (r p : S.I) : ℝ :=
  S.originalAtomMass r * μ.real (S.reverseCompulsorySource {p}) -
    S.emptySatPrivateEdgeMass p

/-- Actual selector charge, retaining the original universal-root star. -/
def emptySatPrivateSelectorCharge (S : SelectedHighLowStructure W m) (r p : S.I) : ℝ :=
  S.emptySatPrivateCharge p + S.originalAtomMass r *
    ∫ x in S.reverseCompulsorySource {p}, S.rootChargeRow r x ∂μ

/-- The signed star of the entire source against one original point. -/
def emptySatPrivateStar (S : SelectedHighLowStructure W m) (p : S.I) (x : Ω) : ℝ :=
  ∫ z in S.reverseCompulsorySource {p}, PhysicalRepresentative.charge W m z x ∂μ

/-- Signed source-to-rest charge; both heads and the entire source are removed. -/
def emptySatPrivateRestCharge (S : SelectedHighLowStructure W m) (r p : S.I) : ℝ :=
  ∫ x in (({x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val}) ∪
    S.reverseCompulsorySource {p})ᶜ, S.emptySatPrivateStar p x ∂μ

/-- Signed charge of the literal old rest after both heads and J are deleted. -/
def emptySatPrivateContextCharge (S : SelectedHighLowStructure W m) (r p : S.I)
    (n : ℕ) (v : Fin n → Ω) : ℝ :=
  let Q := (({x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val}) ∪
    S.reverseCompulsorySource {p})ᶜ
  PhysicalPrimal.charge ((Q ×ˢ Q).indicator
    (Function.uncurry (PhysicalRepresentative.charge W m))) v

/-- The entire original source tests every retained old rest coordinate. -/
def emptySatPrivateContextStar (S : SelectedHighLowStructure W m) (r p : S.I)
    (n : ℕ) (v : Fin n → Ω) : ℝ :=
  let Q := (({x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val}) ∪
    S.reverseCompulsorySource {p})ᶜ
  ∑ i, Q.indicator (S.emptySatPrivateStar p) (v i)

/-- The universal-root charge retained on those same rest coordinates. -/
def emptySatPrivateRootStar (S : SelectedHighLowStructure W m) (r p : S.I)
    (n : ℕ) (v : Fin n → Ω) : ℝ :=
  let Q := (({x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val}) ∪
    S.reverseCompulsorySource {p})ᶜ
  ∑ i, Q.indicator (S.rootChargeRow r) (v i)

omit [MeasurableSpace Ω] in
private def context_indices {n : ℕ} (Q : Set Ω) (v : Fin n → Ω) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => v i ∈ Q)

omit [MeasurableSpace Ω] in
private theorem mem_context_indices {n : ℕ} (Q : Set Ω) (v : Fin n → Ω) (i : Fin n) :
    i ∈ context_indices Q v ↔ v i ∈ Q := by
  classical
  simp only [context_indices, Finset.mem_filter, Finset.mem_univ, true_and]

omit [MeasurableSpace Ω] in
private theorem sum_context_enumeration {n : ℕ} {M : Type*} [AddCommMonoid M]
    (E : Finset (Fin n)) (f : Fin n → M) :
    (∑ i : Fin E.card, f (E.orderEmbOfFin rfl i)) = ∑ i ∈ E, f i := by
  conv_rhs => rw [← Finset.map_orderEmbOfFin_univ E rfl]
  rw [Finset.sum_map]
  rfl

omit [MeasurableSpace Ω] in
private theorem charge_context_tuple (Y : Ω × Ω → ℝ) {n : ℕ} (v : Fin n → Ω) :
    PhysicalPrimal.charge Y v = FiniteArity.tupleCharge (fun x y => Y (x, y)) v := by
  exact MultipartiteHeadPrice.physicalCharge_eq_tupleCharge (fun x y => Y (x, y)) v

omit [MeasurableSpace Ω] in
private theorem charge_context_filter (Q : Set Ω) (Y : Ω × Ω → ℝ)
    {n : ℕ} (v : Fin n → Ω) :
    let E := context_indices Q v
    PhysicalPrimal.charge Y (fun i => v (E.orderEmbOfFin rfl i)) =
      PhysicalPrimal.charge ((Q ×ˢ Q).indicator Y) v := by
  classical
  dsimp only
  let E := context_indices Q v
  rw [charge_context_tuple, charge_context_tuple]
  unfold FiniteArity.tupleCharge FiniteArity.pairCharge FiniteArity.crossSum
  congr 1
  have hinner (i : Fin E.card) :
      (∑ j : Fin E.card, if i = j then 0 else
        Y (v (E.orderEmbOfFin rfl i), v (E.orderEmbOfFin rfl j))) =
      ∑ j ∈ E, if E.orderEmbOfFin rfl i = j then 0 else
        Y (v (E.orderEmbOfFin rfl i), v j) := by
    convert sum_context_enumeration E (fun j =>
      if E.orderEmbOfFin rfl i = j then 0 else Y (v (E.orderEmbOfFin rfl i), v j)) using 1
    simp only [(E.orderEmbOfFin rfl).injective.eq_iff]
  rw [show (∑ i : Fin E.card, ∑ j : Fin E.card, if i = j then 0 else
      Y (v (E.orderEmbOfFin rfl i), v (E.orderEmbOfFin rfl j))) =
        ∑ i : Fin E.card, ∑ j ∈ E,
          if E.orderEmbOfFin rfl i = j then 0 else
            Y (v (E.orderEmbOfFin rfl i), v j) from
      Finset.sum_congr rfl (fun i _ => hinner i),
    sum_context_enumeration E (fun i => ∑ j ∈ E, if i = j then 0 else Y (v i, v j))]
  change (∑ i ∈ Finset.univ.filter (fun i => v i ∈ Q),
    ∑ j ∈ Finset.univ.filter (fun j => v j ∈ Q), if i = j then 0 else Y (v i, v j)) = _
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : v i ∈ Q
  · simp only [hi, ite_true]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : v j ∈ Q <;> by_cases hij : i = j <;>
      simp [Set.indicator, mem_prod, hi, hj, hij]
  · simp [hi, Set.indicator, mem_prod]

omit [MeasurableSpace Ω] in
private theorem sum_context_filter (Q : Set Ω) (f : Ω → ℝ)
    {n : ℕ} (v : Fin n → Ω) :
    let E := context_indices Q v
    (∑ i, f (v (E.orderEmbOfFin rfl i))) = ∑ i, Q.indicator f (v i) := by
  classical
  dsimp only
  rw [sum_context_enumeration (context_indices Q v)
    (fun i => f (v i))]
  unfold context_indices
  rw [Finset.sum_filter]
  exact Finset.sum_congr rfl (fun i _ => by rfl)

variable [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]

namespace UniversalPhysicalPrimal

/-- One actual parent event licenses every old subtuple after deletion.
Only original pair balance is used; joint parents may be singular. -/
theorem ae_emptySat_subtuple_charge_le_one {S : SelectedHighLowStructure W m}
    {r : S.I} {d c : ℝ} (P : S.UniversalPhysicalPrimal r c)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (n : ℕ) :
    ∀ᵐ v ∂P.laws n, ∀ k (e : Fin k ↪ Fin n),
      PhysicalPrimal.charge (Function.uncurry (PhysicalRepresentative.charge W m))
        (fun i => v (e i)) ≤ 1 := by
  let G := Function.uncurry (PhysicalRepresentative.adjacency W m)
  let Y := Function.uncurry (PhysicalRepresentative.charge W m)
  have htest : ∀ k, 2 ≤ k → ∀ᵐ v ∂Measure.pi (fun _ : Fin k => μ),
      PhysicalCliqueRepresentative.Clique G v → PhysicalPrimal.charge Y v ≤ 1 := by
    intro k _
    filter_upwards [PhysicalRepresentative.full_feasible W hW.full m
      (hW.strict_gap_structure hd hgap).strict_support hW.deterministic k]
      with v hv hclique
    rw [MultipartiteHeadPrice.physicalCharge_eq_tupleCharge]
    exact hv hclique
  obtain ⟨Z, _, hZ0, _, _, hlicense⟩ :=
    PhysicalCliqueRepresentative.exists_common_pair_null μ
      (PhysicalRepresentative.measurable_adjacency W m)
      (PhysicalRepresentative.measurable_charge W m) 3 (by norm_num)
      (fun q => PhysicalRepresentative.charge_bound W m q.1 q.2) htest
  have havoid : ∀ᵐ v ∂P.laws n, ∀ i j, i ≠ j → (v i, v j) ∉ Z :=
    PhysicalPrimal.ae_all_pairs_of_balance P.laws _ P.feasible.2.2.2 _
      (ae_restrict_of_ae (compl_mem_ae_iff.mpr hZ0)) n
  filter_upwards [havoid, P.feasible.2.2.1 n] with v hv hc k e
  apply hlicense k (fun i => v (e i))
  · intro i j hij
    exact hc (e i) (e j) (fun h => hij (e.injective h))
  · intro i j hij
    exact hv (e i) (e j) (fun h => hij (e.injective h))

end UniversalPhysicalPrimal

namespace ReverseRecovery

/-- The original source budget pays both positive selector denominators
and the exact nonempty refund before any context division. -/
theorem empty_source_selector_bounds {S : SelectedHighLowStructure W m}
    (R : S.ReverseRecovery) (r p : S.I) (hr : R.plateau = {r})
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (hnull : μ (S.reverseCompulsorySource R.plateau) = 0) :
    let H := S.universalPartnerHoleRegion r p
    let U := S.universalPartnerCommonRegion r p
    let D := (1 - m - 4 * (c - m * d)) / (1 + m)
    let L := μ.real H + μ.real U - D
    let E := D - S.originalAtomMass r
    0 < L → E < L →
      (∀ᵐ x ∂μ.restrict H, S.universalPartnerHoleMissingMass r p x < L) →
      0 < S.emptySatPrivateSelectorRefund r p ∧
        S.emptySatPrivateSelectorRefund r p ≤
          S.originalAtomMass r * μ.real (S.reverseCompulsorySource {p}) ∧
        S.emptySatPrivateSelectorCharge r p ≤ S.emptySatPrivateSelectorRefund r p ∧
        (-m) * S.originalAtomMass r * μ.real (S.reverseCompulsorySource {p}) / 2 <
          S.emptySatPrivateSelectorCharge r p := by
  dsimp only
  intro hL hEL hsmall
  let A := S.originalAtomMass r
  let J := S.reverseCompulsorySource {p}
  let j := μ.real J
  let H := S.universalPartnerHoleRegion r p
  let U := S.universalPartnerCommonRegion r p
  let L := μ.real H + μ.real U - (1 - m - 4 * (c - m * d)) / (1 + m)
  let Sigma := ∫ x in U, -(S.rootChargeRow r x + S.rootChargeRow p x) ∂μ
  let G := PhysicalCliqueRepresentative.edgeIndicator
    (Function.uncurry (PhysicalRepresentative.adjacency W m))
  let Y := Function.uncurry (PhysicalRepresentative.charge W m)
  let e := S.emptySatPrivateEdgeMass p
  let CJ := S.emptySatPrivateCharge p
  let K := S.emptySatPrivateSelectorRefund r p
  let C0 := S.emptySatPrivateSelectorCharge r p
  let nu := μ.restrict J
  obtain ⟨hJ, hj, hmass, hSigma, _, _, hdint, _, _, hbudget, _, _⟩ :=
    R.empty_sat_corner_source_geometry r p hr hpair hW hd hgap hell hnull hL hEL hsmall
  change 0 < j at hj
  have hb : 0 ≤ S.originalAtomMass p := measureReal_nonneg
  have hjA : j < A := by change S.originalAtomMass p + j < A at hmass; linarith
  have hA : 0 < A := hj.trans hjA
  have hm := (hW.strict_gap_structure hd hgap).multiplier_neg
  have hellpos : 0 < -m := neg_pos.mpr hm
  have hG : Integrable G (nu.prod nu) := by
    apply Integrable.of_bound
      (PhysicalCliqueRepresentative.measurable_edgeIndicator
        (PhysicalRepresentative.measurable_adjacency W m)).aestronglyMeasurable 1
    exact Eventually.of_forall (fun q => by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (PhysicalCliqueRepresentative.edgeIndicator_bounds _ _).1]
      exact (PhysicalCliqueRepresentative.edgeIndicator_bounds _ _).2)
  have hY : Integrable Y (nu.prod nu) := Integrable.of_bound
    (PhysicalRepresentative.measurable_charge W m).aestronglyMeasurable 3
    (Eventually.of_forall (fun q => by
      change ‖PhysicalRepresentative.charge W m q.1 q.2‖ ≤ 3
      simpa only [Real.norm_eq_abs] using
        PhysicalRepresentative.charge_bound W m q.1 q.2))
  have he0 : 0 ≤ e := by
    apply div_nonneg _ (by norm_num)
    exact integral_nonneg (fun q =>
      (PhysicalCliqueRepresentative.edgeIndicator_bounds _ q).1)
  have heupper : 2 * e ≤ j ^ 2 := by
    have hi := integral_mono_ae hG (integrable_const (1 : ℝ))
      (Eventually.of_forall (fun q =>
        (PhysicalCliqueRepresentative.edgeIndicator_bounds _ q).2))
    have hmassprod : (nu.prod nu).real univ = j ^ 2 := by
      rw [← univ_prod_univ, measureReal_prod_prod]
      simp only [nu, measureReal_restrict_apply_univ, j, pow_two]
    rw [integral_const, smul_eq_mul, mul_one, hmassprod] at hi
    change (∫ q, G q ∂nu.prod nu) ≤ j ^ 2 at hi
    change 2 * ((∫ q, G q ∂nu.prod nu) / 2) ≤ j ^ 2
    linarith only [hi]
  have hCJ : m * e ≤ CJ := by
    have hle : ∀ᵐ q ∂nu.prod nu, m * G q ≤ Y q := by
      have hdom : nu.prod nu ≤ μ.prod μ :=
        Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
      filter_upwards [ae_mono hdom hW.moment_mem,
        ae_mono hdom (PhysicalRepresentative.charge_ae_eq W m
          (hW.strict_gap_structure hd hgap).strict_support),
        ae_mono hdom (PhysicalRepresentative.adjacency_moment_ae_eq W m
          (hW.strict_gap_structure hd hgap).strict_support)] with q hM hYq hGq
      have heq := shiftedMoment_eq W m q
      change shiftedKernel W m q.1 q.2 = chargeKernel W q.1 q.2 -
        m * adjacencyKernel W q.1 q.2 at heq
      change adjacencyKernel W q.1 q.2 = G q at hGq
      rw [← hYq, hGq] at heq
      change shiftedKernel W m q.1 q.2 = Y q - m * G q at heq
      change m * G q ≤ Y q
      have hn : 0 ≤ shiftedKernel W m q.1 q.2 := hM.1
      linarith only [hn, heq]
    have hi := integral_mono_ae (hG.const_mul m) hY hle
    rw [integral_const_mul] at hi
    change m * ((∫ q, G q ∂nu.prod nu) / 2) ≤
      (∫ q, Y q ∂nu.prod nu) / 2
    linarith only [hi]
  have hbeta : Integrable (S.rootChargeRow r) nu := by
    apply Integrable.of_bound (S.measurable_rootChargeRow r).aestronglyMeasurable 3
    exact Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨(S.rootChargeRow_mem_Icc r x).1,
        (S.rootChargeRow_mem_Icc r x).2.trans (by norm_num)⟩)
  have hbetaeq : (∫ x in J, S.rootChargeRow r x ∂μ) =
      j - ∫ x in J, S.universalRootDeficit r x ∂μ := by
    have hi := integral_sub (integrable_const (μ := nu) (1 : ℝ)) hbeta
    change (∫ x in J, S.universalRootDeficit r x ∂μ) = _ at hi
    rw [integral_const, smul_eq_mul, mul_one] at hi
    rw [show nu.real univ = j by simp only [nu, measureReal_restrict_apply_univ, j]] at hi
    change (∫ x in J, S.universalRootDeficit r x ∂μ) =
      j - ∫ x in J, S.rootChargeRow r x ∂μ at hi
    linarith only [hi]
  have hC0 : C0 = CJ + A * (j - ∫ x in J, S.universalRootDeficit r x ∂μ) := by
    exact congrArg (fun x => CJ + A * x) hbetaeq
  have hK : K = A * j - e := rfl
  have hKpos : 0 < K := by
    have hprod := mul_pos hj (sub_pos.mpr hjA)
    rw [hK]
    nlinarith only [heupper, hprod, sq_nonneg j]
  have hKcap : K ≤ A * j := by rw [hK]; linarith only [he0]
  have hC0K : C0 ≤ K := R.empty_source_private_selector_bound r p hpair hr
    hW hd hgap hell hnull
  have hpaid := mul_le_mul_of_nonneg_left hbudget hA.le
  have hepaid := mul_le_mul_of_nonpos_left heupper hm.le
  have hsigpaid := mul_nonneg hA.le hSigma
  have hcross := mul_pos hellpos (mul_pos hj (sub_pos.mpr hjA))
  have hLP := mul_pos hA (mul_pos (show 0 < 1 + m by linarith only [hell]) hL)
  have hC0pos : (-m) * A * j / 2 < C0 := by
    change (∫ x in J, S.universalRootDeficit r x ∂μ) ≤
      (1 + m) * (j - L) - Sigma at hbudget
    change A * (∫ x in J, S.universalRootDeficit r x ∂μ) ≤
      A * ((1 + m) * (j - L) - Sigma) at hpaid
    rw [hC0]
    nlinarith only [hCJ, hepaid, hpaid, hsigpaid, hcross, hLP]
  exact ⟨hKpos, hKcap, hC0K, hC0pos⟩

end ReverseRecovery

namespace UniversalPhysicalPrimal

/-- Old headless-hole columns pay their own exact signed deletion slack. -/
def emptySatPrivateDeletionSlack {S : SelectedHighLowStructure W m} {r : S.I} {c : ℝ}
    (P : S.UniversalPhysicalPrimal r c) (p : S.I) : ℝ :=
  ∑ n ∈ Finset.range (P.orderCap + 1),
    ∫ v, 1 - S.emptySatPrivateContextCharge r p n v ∂P.emptySatHoleLaws p n

/-- Every actual old rest remains a licensed subclique under its parent law. -/
theorem ae_emptySat_private_context_charge_le_one {S : SelectedHighLowStructure W m}
    {r : S.I} {d c : ℝ} (P : S.UniversalPhysicalPrimal r c) (p : S.I)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (n : ℕ) :
    ∀ᵐ v ∂P.laws n, S.emptySatPrivateContextCharge r p n v ≤ 1 := by
  classical
  let Q := (({x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val}) ∪
    S.reverseCompulsorySource {p})ᶜ
  filter_upwards [P.ae_emptySat_subtuple_charge_le_one hW hd hgap n] with v hv
  let E := context_indices Q v
  have hb := hv E.card (E.orderEmbOfFin rfl).toEmbedding
  have he := charge_context_filter Q
    (Function.uncurry (PhysicalRepresentative.charge W m)) v
  dsimp only at he
  dsimp only [E] at hb
  exact he.symm.le.trans hb

/-- Feasibility of those same deleted old subcliques makes the slack nonnegative. -/
theorem emptySatPrivateDeletionSlack_nonneg {S : SelectedHighLowStructure W m}
    {r : S.I} {d c : ℝ} (P : S.UniversalPhysicalPrimal r c) (p : S.I)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    0 ≤ P.emptySatPrivateDeletionSlack p := by
  apply Finset.sum_nonneg
  intro n _
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_of_ae
    (P.ae_emptySat_private_context_charge_le_one p hW hd hgap n)] with v hv
  exact sub_nonneg.mpr hv

end UniversalPhysicalPrimal

namespace ReverseRecovery

/-- The original source selector tests measurable signed functions of each
same old parent, with the exact nonempty refund. -/
theorem ae_emptySat_context_selector_sum {S : SelectedHighLowStructure W m}
    (R : S.ReverseRecovery) (r p : S.I) (hr : R.plateau = {r})
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (P : S.UniversalPhysicalPrimal r c) (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (hnull : μ (S.reverseCompulsorySource R.plateau) = 0) (n : ℕ) :
    ∀ᵐ v ∂P.laws n,
      S.emptySatPrivateSelectorCharge r p +
        S.originalAtomMass r * S.emptySatPrivateContextStar r p n v ≤
      S.emptySatPrivateSelectorRefund r p *
        (1 - S.emptySatPrivateContextCharge r p n v - S.emptySatPrivateRootStar r p n v) := by
  classical
  let Q := (({x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val}) ∪
    S.reverseCompulsorySource {p})ᶜ
  filter_upwards [R.empty_source_context_selector r p hr hpair P hW hd hgap hell hnull n]
    with v hv
  let E := context_indices Q v
  have hQ : ∀ i : Fin E.card, v (E.orderEmbOfFin rfl i) ∈ Q := by
    intro i
    have he := E.orderEmbOfFin_mem rfl i
    exact (mem_context_indices Q v _).mp he
  have hb := hv E.card (E.orderEmbOfFin rfl).toEmbedding hQ
  have hcharge := charge_context_filter Q
    (Function.uncurry (PhysicalRepresentative.charge W m)) v
  have hroot := sum_context_filter Q (S.rootChargeRow r) v
  have hstar := sum_context_filter Q (S.emptySatPrivateStar p) v
  dsimp only at hcharge hroot hstar
  conv_lhs at hstar => simp only [emptySatPrivateStar]
  change S.emptySatPrivateCharge p + S.originalAtomMass r *
      (∫ x in S.reverseCompulsorySource {p}, S.rootChargeRow r x ∂μ) +
      S.originalAtomMass r * (∑ i, ∫ x in S.reverseCompulsorySource {p},
        PhysicalRepresentative.charge W m x (v (E.orderEmbOfFin rfl i)) ∂μ) ≤
    S.emptySatPrivateSelectorRefund r p *
      (1 - PhysicalPrimal.charge (Function.uncurry (PhysicalRepresentative.charge W m))
        (fun i => v (E.orderEmbOfFin rfl i)) -
          ∑ i, S.rootChargeRow r (v (E.orderEmbOfFin rfl i))) at hb
  dsimp only [E] at hb
  have hleft : S.emptySatPrivateSelectorCharge r p +
      S.originalAtomMass r * S.emptySatPrivateContextStar r p n v =
      S.emptySatPrivateCharge p + S.originalAtomMass r *
        (∫ x in S.reverseCompulsorySource {p}, S.rootChargeRow r x ∂μ) +
        S.originalAtomMass r * (∑ i, ∫ x in S.reverseCompulsorySource {p},
          PhysicalRepresentative.charge W m x (v (E.orderEmbOfFin rfl i)) ∂μ) :=
    congrArg (fun t => S.emptySatPrivateCharge p + S.originalAtomMass r *
      (∫ x in S.reverseCompulsorySource {p}, S.rootChargeRow r x ∂μ) +
        S.originalAtomMass r * t) hstar.symm
  have hright : S.emptySatPrivateSelectorRefund r p *
      (1 - PhysicalPrimal.charge (Function.uncurry (PhysicalRepresentative.charge W m))
        (fun i => v (E.orderEmbOfFin rfl i)) -
          ∑ i, S.rootChargeRow r (v (E.orderEmbOfFin rfl i))) =
      S.emptySatPrivateSelectorRefund r p *
        (1 - S.emptySatPrivateContextCharge r p n v -
          S.emptySatPrivateRootStar r p n v) :=
    congrArg (fun t => S.emptySatPrivateSelectorRefund r p * t)
      (congrArg₂ (fun a b : ℝ => a - b) (congrArg (fun a : ℝ => 1 - a) hcharge) hroot)
  exact hleft.le.trans (hb.trans_eq hright)

end ReverseRecovery


end Erdos1017.CappedModel.SelectedHighLowStructure
