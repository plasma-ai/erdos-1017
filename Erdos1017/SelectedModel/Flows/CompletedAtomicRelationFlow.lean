module

public import Erdos1017.SelectedModel.Structure.NormalizedAtomicFractions
public import Erdos1017.SelectedModel.Flows.RestrictedAtomicAssignmentFlow
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Full flow combining atomic assignment and diffuse remainder

A completed atomic assignment and the normalized remaining recipient flow
combine into a nonnegative product density with full supply on its source
region, an integrable mean-zero direction, support on the original relation, and
exact endpoint masses on disjoint atoms.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set

namespace Erdos1017.MissingFlow.CompletedAtomicRelation

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- The original relation with recipients in the literal complement of all parts. -/
def diffuseRelation (Z : Set (Ω × Ω)) (I : ℕ → Set Ω) : Set (Ω × Ω) :=
  Z ∩ ((⋃ i, I i)ᶜ ×ˢ univ)

/-- The completed atomic assignment and the normalized remaining recipient flow. -/
def density (μ : Measure Ω) (H : Set Ω) (Z : Set (Ω × Ω)) (I : ℕ → Set Ω)
    (q : ℕ → Lp ℝ 2 (μ.restrict H)) : Ω × Ω → ℝ :=
  RestrictedAtomicAssignment.density μ H I q + normalizedDensity μ (diffuseRelation Z I)

variable {H : Set Ω} {Z : Set (Ω × Ω)} {I : ℕ → Set Ω}
  {q : ℕ → Lp ℝ 2 (μ.restrict H)}

private theorem measurableSet_diffuseRelation (hZ : MeasurableSet Z)
    (hI : ∀ i, MeasurableSet (I i)) : MeasurableSet (diffuseRelation Z I) :=
  hZ.inter ((MeasurableSet.iUnion hI).compl.prod MeasurableSet.univ)

omit [IsFiniteMeasure μ] in
private theorem diffuse_columnMass (y : Ω) :
    columnMass μ (diffuseRelation Z I) y =
      NormalizedAtomicFractions.remainderSectionMass μ Z I y := by
  unfold columnMass NormalizedAtomicFractions.remainderSectionMass diffuseRelation
  congr 1
  ext x
  simp only [mem_ofPred_eq, mem_inter_iff, mem_prod, mem_univ, and_true]
  exact and_comm

private theorem diffuse_positiveSources_subset :
    positiveSources μ (diffuseRelation Z I) ⊆ positiveSources μ Z := by
  intro y hy
  have hle : columnMass μ (diffuseRelation Z I) y ≤ columnMass μ Z y :=
    measureReal_mono (fun _ hx => hx.1)
  exact lt_of_lt_of_le hy hle

omit [IsFiniteMeasure μ] in
private theorem coordinate_nonneg
    (hq : ReverseAssignment.Feasible (NormalizedAtomicFractions.allowed μ Z I)
      (NormalizedAtomicFractions.remainderSectionMass μ Z I) q) (i : ℕ) :
    ∀ᵐ x ∂μ.restrict H, 0 ≤ q i x :=
  (hq.box i).mono (fun _ hx => hx.1)

private theorem receipt_summable
    (hq : ReverseAssignment.Feasible (NormalizedAtomicFractions.allowed μ Z I)
      (NormalizedAtomicFractions.remainderSectionMass μ Z I) q) :
    Summable (fun i => ∫ x, q i x ∂μ.restrict H) := by
  have hs := hq.mass_summable (a := fun _ => 0) (fun _ => le_rfl) summable_zero
  change Summable (fun i => (0 : ℝ) + ∫ x, q i x ∂μ.restrict H) at hs
  simpa only [zero_add] using hs

private theorem inactive_coordinate
    (hq : ReverseAssignment.Feasible (NormalizedAtomicFractions.allowed μ Z I)
      (NormalizedAtomicFractions.remainderSectionMass μ Z I) q)
    (i : ℕ) (hi : μ (I i) = 0) : (q i : Ω → ℝ) =ᵐ[μ.restrict H] 0 := by
  have hnot (y : Ω) : y ∉ NormalizedAtomicFractions.allowed μ Z I i := by
    have hle : NormalizedAtomicFractions.atomSectionMass μ Z I i y ≤ μ.real (I i) :=
      measureReal_mono inter_subset_left
    have hzero : μ.real (I i) = 0 := by simp only [measureReal_def, hi, ENNReal.toReal_zero]
    exact not_lt_of_ge (hzero ▸ hle)
  filter_upwards [hq.support i] with y hy
  exact hy (hnot y)

private theorem atomic_properties (hH : MeasurableSet H)
    (hI : ∀ i, MeasurableSet (I i))
    (hq : ReverseAssignment.Feasible (NormalizedAtomicFractions.allowed μ Z I)
      (NormalizedAtomicFractions.remainderSectionMass μ Z I) q) :
    (∀ i, Integrable (RestrictedAtomicAssignment.liftFraction H q i) μ ∧
      (∀ᵐ x ∂μ, 0 ≤ RestrictedAtomicAssignment.liftFraction H q i x) ∧
      (∫ x, RestrictedAtomicAssignment.liftFraction H q i x ∂μ) =
        (∫ x, q i x ∂μ.restrict H) ∧
      (μ (I i) = 0 → RestrictedAtomicAssignment.liftFraction H q i =ᵐ[μ] 0)) ∧
      Integrable (RestrictedAtomicAssignment.density μ H I q) (μ.prod μ) ∧
      (∀ᵐ p ∂μ.prod μ, 0 ≤ RestrictedAtomicAssignment.density μ H I q p) ∧
      (∫ p, RestrictedAtomicAssignment.density μ H I q p ∂μ.prod μ) =
        ∑' i, ∫ x, q i x ∂μ.restrict H :=
  RestrictedAtomicAssignment.lift_assignment_properties H hH I hI q
    (coordinate_nonneg hq) (inactive_coordinate hq) (receipt_summable hq)

/-- The two constructed components give a genuine nonnegative original product density. -/
theorem integrable_nonnegative (hZ : MeasurableSet Z) (hH : MeasurableSet H)
    (hI : ∀ i, MeasurableSet (I i))
    (hq : ReverseAssignment.Feasible (NormalizedAtomicFractions.allowed μ Z I)
      (NormalizedAtomicFractions.remainderSectionMass μ Z I) q) :
    Integrable (density μ H Z I q) (μ.prod μ) ∧
      ∀ᵐ p ∂μ.prod μ, 0 ≤ density μ H Z I q p := by
  have ha := atomic_properties hH hI hq
  have hd := integrable_normalizedDensity (μ := μ) _ (measurableSet_diffuseRelation hZ hI)
  refine ⟨ha.2.1.add hd, ?_⟩
  filter_upwards [ha.2.2.1] with p hp
  exact add_nonneg hp (normalizedDensity_nonneg _ p)

/-- Completion on zero remainder sections and zero atomic fractions elsewhere
give full supply on the actual source region, with its exact original mass. -/
theorem supply_density (hZ : MeasurableSet Z) (hH : MeasurableSet H)
    (hI : ∀ i, MeasurableSet (I i))
    (hsources : ∀ᵐ y ∂μ, y ∈ positiveSources μ Z ↔ y ∈ H)
    (hq : ReverseAssignment.Feasible (NormalizedAtomicFractions.allowed μ Z I)
      (NormalizedAtomicFractions.remainderSectionMass μ Z I) q)
    (hfull : ∀ᵐ y ∂μ.restrict H,
      NormalizedAtomicFractions.remainderSectionMass μ Z I y = 0 →
        HasSum (fun i => q i y) 1)
    (hzeroDiffuse : ∀ᵐ y ∂μ.restrict H,
      NormalizedAtomicFractions.remainderSectionMass μ Z I y ≠ 0 → ∀ i, q i y = 0) :
    supply μ (density μ H Z I q) =ᵐ[μ] H.indicator (fun _ => 1) ∧
      (∫ p, density μ H Z I q p ∂μ.prod μ) = μ.real H := by
  let δ := NormalizedAtomicFractions.remainderSectionMass μ Z I
  have hsource : ∀ᵐ y ∂μ.restrict H,
      HasSum (fun i => q i y) ({y | δ y = 0}.indicator (fun _ => 1) y) := by
    filter_upwards [hfull, hzeroDiffuse] with y hf hz
    by_cases hy : δ y = 0
    · simpa only [indicator_of_mem (show y ∈ {y | δ y = 0} from hy)] using hf hy
    · rw [indicator_of_notMem (show y ∉ {y | δ y = 0} from hy)]
      convert (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0) using 1
      funext i
      exact hz hy i
  have ha := RestrictedAtomicAssignment.hasSum_supply H hH I hI q
    (coordinate_nonneg hq) (inactive_coordinate hq) (receipt_summable hq) _ hsource
  have hZd := measurableSet_diffuseRelation hZ hI
  have hia := (atomic_properties hH hI hq).2.1
  have hid := integrable_normalizedDensity (μ := μ) _ hZd
  have hs : supply μ (density μ H Z I q) =ᵐ[μ] H.indicator (fun _ => 1) := by
    filter_upwards [ha, hia.prod_left_ae, hid.prod_left_ae, hsources] with y hy hiy hdy hH
    change (∫ x, RestrictedAtomicAssignment.density μ H I q (x, y) +
      normalizedDensity μ (diffuseRelation Z I) (x, y) ∂μ) = _
    rw [integral_add hiy hdy]
    change supply μ (RestrictedAtomicAssignment.density μ H I q) y +
      supply μ (normalizedDensity μ (diffuseRelation Z I)) y = _
    rw [hy.2, supply_normalizedDensity _ hZd]
    by_cases hz : δ y = 0
    · have hn : y ∉ positiveSources μ (diffuseRelation Z I) := by
        change ¬ 0 < columnMass μ (diffuseRelation Z I) y
        rw [diffuse_columnMass]
        exact not_lt_of_ge (le_of_eq hz)
      by_cases hyH : y ∈ H
      · simp only [indicator_of_mem hyH,
          indicator_of_mem (show y ∈ {y | δ y = 0} from hz),
          indicator_of_notMem hn, add_zero]
      · simp only [indicator_of_notMem hyH, indicator_of_notMem hn, add_zero]
    · have hp : y ∈ positiveSources μ (diffuseRelation Z I) := by
        change 0 < columnMass μ (diffuseRelation Z I) y
        rw [diffuse_columnMass]
        exact lt_of_le_of_ne measureReal_nonneg (Ne.symm hz)
      have hyH : y ∈ H := hH.mp (diffuse_positiveSources_subset hp)
      simp only [indicator_of_notMem (show y ∉ {y | δ y = 0} from hz),
        indicator_of_mem hp, indicator_of_mem hyH, zero_add]
  refine ⟨hs, ?_⟩
  rw [← (integral_marginals (integrable_nonnegative hZ hH hI hq).1).2,
    integral_congr_ae hs, integral_indicator hH, setIntegral_const]
  simp

/-- The constructed full flow has an integrable mean-zero direction and a
nonnegative endpoint density on the original law. -/
theorem direction_properties (hZ : MeasurableSet Z) (hH : MeasurableSet H)
    (hI : ∀ i, MeasurableSet (I i))
    (hsources : ∀ᵐ y ∂μ, y ∈ positiveSources μ Z ↔ y ∈ H)
    (hq : ReverseAssignment.Feasible (NormalizedAtomicFractions.allowed μ Z I)
      (NormalizedAtomicFractions.remainderSectionMass μ Z I) q)
    (hfull : ∀ᵐ y ∂μ.restrict H,
      NormalizedAtomicFractions.remainderSectionMass μ Z I y = 0 →
        HasSum (fun i => q i y) 1)
    (hzeroDiffuse : ∀ᵐ y ∂μ.restrict H,
      NormalizedAtomicFractions.remainderSectionMass μ Z I y ≠ 0 → ∀ i, q i y = 0) :
    Integrable (direction μ (density μ H Z I q)) μ ∧
      (∫ x, direction μ (density μ H Z I q) x ∂μ) = 0 ∧
      ∀ᵐ x ∂μ, -1 ≤ direction μ (density μ H Z I q) x := by
  have hi := integrable_nonnegative hZ hH hI hq
  refine ⟨integrable_direction hi.1, integral_direction hi.1, direction_ge_neg_one hi.2 ?_⟩
  filter_upwards [(supply_density hZ hH hI hsources hq hfull hzeroDiffuse).1] with x hx
  rw [hx]
  by_cases hmem : x ∈ H
  · simp only [indicator_of_mem hmem, le_refl]
  · simp only [indicator_of_notMem hmem, zero_le_one]

/-- Original product rectangle licenses and the literal remainder relation
keep the entire constructed density on the original relation. -/
theorem supported_density (hH : MeasurableSet H)
    (hq : ReverseAssignment.Feasible (NormalizedAtomicFractions.allowed μ Z I)
      (NormalizedAtomicFractions.remainderSectionMass μ Z I) q)
    (hrect : ∀ i, ∀ᵐ p ∂μ.prod μ, p.1 ∈ I i →
      p.2 ∈ H ∩ NormalizedAtomicFractions.allowed μ Z I i → p ∈ Z) :
    ∀ᵐ p ∂μ.prod μ, p ∉ Z → density μ H Z I q p = 0 := by
  have ha := RestrictedAtomicAssignment.supported_density H hH I
    (NormalizedAtomicFractions.allowed μ Z I) q Z hq.support hrect
  filter_upwards [ha] with p hp hnot
  have hd : p ∉ diffuseRelation Z I := fun h => hnot h.1
  change RestrictedAtomicAssignment.density μ H I q p +
    normalizedDensity μ (diffuseRelation Z I) p = 0
  rw [hp hnot, normalizedDensity_eq_zero_of_notMem _ p hd, add_zero]

private theorem endpoint_mass_of_supply {Q : Ω × Ω → ℝ} (hH : MeasurableSet H)
    (hQ : Integrable Q (μ.prod μ))
    (hs : supply μ Q =ᵐ[μ] H.indicator (fun _ => 1)) (A : Set Ω) :
    (∫ x in A, (1 + direction μ Q x) ∂μ) =
      μ.real (A \ H) + ∫ x in A, receipt μ Q x ∂μ := by
  have heq : (fun x => 1 + direction μ Q x) =ᵐ[μ.restrict A]
      (fun x => Hᶜ.indicator (fun _ => (1 : ℝ)) x + receipt μ Q x) := by
    filter_upwards [ae_restrict_of_ae hs] with x hx
    by_cases hmem : x ∈ H
    · simp only [direction, hx, indicator_of_mem hmem,
        indicator_of_notMem (show x ∉ Hᶜ from not_not.mpr hmem)]
      ring
    · simp only [direction, hx, indicator_of_notMem hmem,
        indicator_of_mem (show x ∈ Hᶜ from hmem), sub_zero]
  rw [integral_congr_ae heq,
    integral_add ((integrable_const (1 : ℝ)).indicator hH.compl)
      (integrable_marginals hQ).1.integrableOn,
    setIntegral_indicator hH.compl, setIntegral_const]
  simp only [sdiff_eq, smul_eq_mul, mul_one]

/-- Each disjoint original atom retains its mass outside the source region
and gains exactly its restricted assignment receipt, including HIGH atoms. -/
theorem endpoint_mass_on_atom (hZ : MeasurableSet Z) (hH : MeasurableSet H)
    (hI : ∀ i, MeasurableSet (I i))
    (hsources : ∀ᵐ y ∂μ, y ∈ positiveSources μ Z ↔ y ∈ H)
    (hq : ReverseAssignment.Feasible (NormalizedAtomicFractions.allowed μ Z I)
      (NormalizedAtomicFractions.remainderSectionMass μ Z I) q)
    (hfull : ∀ᵐ y ∂μ.restrict H,
      NormalizedAtomicFractions.remainderSectionMass μ Z I y = 0 →
        HasSum (fun i => q i y) 1)
    (hzeroDiffuse : ∀ᵐ y ∂μ.restrict H,
      NormalizedAtomicFractions.remainderSectionMass μ Z I y ≠ 0 → ∀ i, q i y = 0)
    (hdisjoint : Pairwise (fun j k => Disjoint (I j) (I k))) (i : ℕ) :
    (∫ x in I i, (1 + direction μ (density μ H Z I q) x) ∂μ) =
      μ.real (I i \ H) + ∫ x, q i x ∂μ.restrict H := by
  have ha := atomic_properties hH hI hq
  have hd := integrable_normalizedDensity (μ := μ) _ (measurableSet_diffuseRelation hZ hI)
  have hr : receipt μ (density μ H Z I q) =ᵐ[μ]
      (fun x => receipt μ (RestrictedAtomicAssignment.density μ H I q) x +
        receipt μ (normalizedDensity μ (diffuseRelation Z I)) x) := by
    filter_upwards [ha.2.1.prod_right_ae, hd.prod_right_ae] with x hax hdx
    exact integral_add hax hdx
  have hdiff (x : Ω) (hx : x ∈ I i) :
      receipt μ (normalizedDensity μ (diffuseRelation Z I)) x = 0 :=
    receipt_normalizedDensity_eq_zero (diffuseRelation Z I) (⋃ j, I j)ᶜ
      (fun _ hp => hp.2.1) x (fun hxR => hxR (mem_iUnion.mpr ⟨i, hx⟩))
  have heq : receipt μ (density μ H Z I q) =ᵐ[μ.restrict (I i)]
      receipt μ (RestrictedAtomicAssignment.density μ H I q) := by
    filter_upwards [ae_restrict_of_ae hr, ae_restrict_mem (hI i)] with x hx hxi
    rw [hx, hdiff x hxi, add_zero]
  rw [endpoint_mass_of_supply hH (integrable_nonnegative hZ hH hI hq).1
    (supply_density hZ hH hI hsources hq hfull hzeroDiffuse).1,
    integral_congr_ae heq]
  change μ.real (I i \ H) +
    (∫ x in I i, receipt μ (AtomicAssignment.density μ I
      (RestrictedAtomicAssignment.liftFraction H q)) x ∂μ) = _
  rw [AtomicAssignment.receipt_mass I hI _ hdisjoint i (ha.1 i).2.2.2,
    (ha.1 i).2.2.1]

end Erdos1017.MissingFlow.CompletedAtomicRelation
