module

public import Erdos1017.SelectedModel.Flows.AtomicAssignmentFlow
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Tactic.NormNum

/-!
# Atomic assignment flow from a restricted source law

Fractions on the restricted source law extend by zero to the original law and
give a product density that preserves every receipt mass, supplies its source
series with zero supply outside that region, has an `L1` mean-zero direction,
and is supported on the original relation.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set

namespace Erdos1017.MissingFlow.RestrictedAtomicAssignment

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- A fraction on the restricted source law, extended by zero to the original law. -/
def liftFraction (H : Set Ω) (q : ℕ → Lp ℝ 2 (μ.restrict H)) (i : ℕ) : Ω → ℝ :=
  H.indicator (fun x => q i x)

/-- The actual atomic assignment flow on the original product measure. -/
def density (μ : Measure Ω) (H : Set Ω) (I : ℕ → Set Ω)
    (q : ℕ → Lp ℝ 2 (μ.restrict H)) : Ω × Ω → ℝ :=
  AtomicAssignment.density μ I (liftFraction H q)

private theorem integrable_lift (H : Set Ω) (hH : MeasurableSet H)
    (q : ℕ → Lp ℝ 2 (μ.restrict H)) (i : ℕ) : Integrable (liftFraction H q i) μ := by
  apply (integrable_indicator_iff hH).mpr
  exact (Lp.memLp (q i)).integrable (by norm_num)

omit [IsFiniteMeasure μ] in
private theorem integral_lift (H : Set Ω) (hH : MeasurableSet H)
    (q : ℕ → Lp ℝ 2 (μ.restrict H)) (i : ℕ) :
    (∫ x, liftFraction H q i x ∂μ) = ∫ x, q i x ∂μ.restrict H :=
  integral_indicator hH

omit [IsFiniteMeasure μ] in
private theorem nonnegative_lift (H : Set Ω) (hH : MeasurableSet H)
    (q : ℕ → Lp ℝ 2 (μ.restrict H)) (i : ℕ)
    (hq : ∀ᵐ x ∂μ.restrict H, 0 ≤ q i x) :
    ∀ᵐ x ∂μ, 0 ≤ liftFraction H q i x := by
  filter_upwards [(ae_restrict_iff' hH).mp hq] with x hx
  by_cases hmem : x ∈ H
  · simpa only [liftFraction, indicator_of_mem hmem] using hx hmem
  · simp only [liftFraction, indicator_of_notMem hmem, le_refl]

omit [IsFiniteMeasure μ] in
private theorem zero_lift (H : Set Ω) (hH : MeasurableSet H)
    (q : ℕ → Lp ℝ 2 (μ.restrict H)) (i : ℕ)
    (hq : (q i : Ω → ℝ) =ᵐ[μ.restrict H] 0) :
    liftFraction H q i =ᵐ[μ] 0 :=
  indicator_ae_eq_zero_of_restrict_ae_eq_zero hH hq

omit [IsFiniteMeasure μ] in
private theorem summable_lift (H : Set Ω) (hH : MeasurableSet H)
    (q : ℕ → Lp ℝ 2 (μ.restrict H))
    (hsum : Summable (fun i => ∫ x, q i x ∂μ.restrict H)) :
    Summable (fun i => ∫ x, liftFraction H q i x ∂μ) :=
  hsum.congr (fun i => (integral_lift H hH q i).symm)

/-- Restricted L² fractions give original-law L¹ fractions and a genuine
original product density, preserving all individual and total receipt masses. -/
theorem lift_assignment_properties (H : Set Ω) (hH : MeasurableSet H)
    (I : ℕ → Set Ω) (hI : ∀ i, MeasurableSet (I i))
    (q : ℕ → Lp ℝ 2 (μ.restrict H))
    (hq0 : ∀ i, ∀ᵐ x ∂μ.restrict H, 0 ≤ q i x)
    (hzero : ∀ i, μ (I i) = 0 → (q i : Ω → ℝ) =ᵐ[μ.restrict H] 0)
    (hsum : Summable (fun i => ∫ x, q i x ∂μ.restrict H)) :
    (∀ i, Integrable (liftFraction H q i) μ ∧
      (∀ᵐ x ∂μ, 0 ≤ liftFraction H q i x) ∧
      (∫ x, liftFraction H q i x ∂μ) = (∫ x, q i x ∂μ.restrict H) ∧
      (μ (I i) = 0 → liftFraction H q i =ᵐ[μ] 0)) ∧
      Integrable (density μ H I q) (μ.prod μ) ∧
      (∀ᵐ p ∂μ.prod μ, 0 ≤ density μ H I q p) ∧
      (∫ p, density μ H I q p ∂μ.prod μ) = ∑' i, ∫ x, q i x ∂μ.restrict H := by
  have hi := integrable_lift H hH q
  have hn := fun i => nonnegative_lift H hH q i (hq0 i)
  have hz := fun i h => zero_lift H hH q i (hzero i h)
  have hs := summable_lift H hH q hsum
  refine ⟨fun i => ⟨hi i, hn i, integral_lift H hH q i, hz i⟩,
    AtomicAssignment.integrable_density I hI _ hi hn hz hs,
    AtomicAssignment.nonnegative_density I _ hn, ?_⟩
  rw [density, AtomicAssignment.integral_density I hI _ hi hn hz hs]
  exact tsum_congr (integral_lift H hH q)

/-- A source-series identity on the restricted law becomes the actual
original-law supply identity, with zero supply outside the source region. -/
theorem hasSum_supply (H : Set Ω) (hH : MeasurableSet H)
    (I : ℕ → Set Ω) (hI : ∀ i, MeasurableSet (I i))
    (q : ℕ → Lp ℝ 2 (μ.restrict H))
    (hq0 : ∀ i, ∀ᵐ x ∂μ.restrict H, 0 ≤ q i x)
    (hzero : ∀ i, μ (I i) = 0 → (q i : Ω → ℝ) =ᵐ[μ.restrict H] 0)
    (hsum : Summable (fun i => ∫ x, q i x ∂μ.restrict H)) (r : Ω → ℝ)
    (hsource : ∀ᵐ x ∂μ.restrict H, HasSum (fun i => q i x) (r x)) :
    ∀ᵐ x ∂μ, HasSum (fun i => liftFraction H q i x) (H.indicator r x) ∧
      supply μ (density μ H I q) x = H.indicator r x := by
  have hlift : ∀ᵐ x ∂μ, HasSum (fun i => liftFraction H q i x) (H.indicator r x) := by
    filter_upwards [(ae_restrict_iff' hH).mp hsource] with x hx
    by_cases hmem : x ∈ H
    · simpa only [liftFraction, indicator_of_mem hmem] using hx hmem
    · simp only [liftFraction, indicator_of_notMem hmem]
      exact hasSum_zero
  have hactual := AtomicAssignment.hasSum_supply I hI (liftFraction H q)
    (integrable_lift H hH q) (fun i => nonnegative_lift H hH q i (hq0 i))
    (fun i h => zero_lift H hH q i (hzero i h)) (summable_lift H hH q hsum)
  filter_upwards [hlift, hactual] with x hx hy
  exact ⟨hx, hy.unique hx⟩

/-- The restricted source-series cap pays the actual original-law endpoint
weight, while its direction is genuinely L¹ and has zero original mean. -/
theorem direction_properties (H : Set Ω) (hH : MeasurableSet H)
    (I : ℕ → Set Ω) (hI : ∀ i, MeasurableSet (I i))
    (q : ℕ → Lp ℝ 2 (μ.restrict H))
    (hq0 : ∀ i, ∀ᵐ x ∂μ.restrict H, 0 ≤ q i x)
    (hzero : ∀ i, μ (I i) = 0 → (q i : Ω → ℝ) =ᵐ[μ.restrict H] 0)
    (hsum : Summable (fun i => ∫ x, q i x ∂μ.restrict H))
    (hcap : ∀ᵐ x ∂μ.restrict H, (∑' i, q i x) ≤ 1) :
    Integrable (direction μ (density μ H I q)) μ ∧
      (∫ x, direction μ (density μ H I q) x ∂μ) = 0 ∧
      ∀ᵐ x ∂μ, -1 ≤ direction μ (density μ H I q) x := by
  have hcap' : ∀ᵐ x ∂μ, (∑' i, liftFraction H q i x) ≤ 1 := by
    filter_upwards [(ae_restrict_iff' hH).mp hcap] with x hx
    by_cases hmem : x ∈ H
    · simpa only [liftFraction, indicator_of_mem hmem] using hx hmem
    · simp only [liftFraction, indicator_of_notMem hmem, tsum_zero, zero_le_one]
  exact AtomicAssignment.direction_properties I hI (liftFraction H q)
    (integrable_lift H hH q) (fun i => nonnegative_lift H hH q i (hq0 i))
    (fun i h => zero_lift H hH q i (hzero i h)) (summable_lift H hH q hsum) hcap'

/-- An original atom disjoint from the source region up to a null set gains
exactly its restricted-law receipt; its retained mass is the original mass. -/
theorem endpoint_mass_on_atom (H : Set Ω) (hH : MeasurableSet H)
    (I : ℕ → Set Ω) (hI : ∀ i, MeasurableSet (I i))
    (q : ℕ → Lp ℝ 2 (μ.restrict H))
    (hq0 : ∀ i, ∀ᵐ x ∂μ.restrict H, 0 ≤ q i x)
    (hzero : ∀ i, μ (I i) = 0 → (q i : Ω → ℝ) =ᵐ[μ.restrict H] 0)
    (hsum : Summable (fun i => ∫ x, q i x ∂μ.restrict H))
    (hdisjoint : Pairwise (fun j k => Disjoint (I j) (I k))) (i : ℕ)
    (hHI : μ (H ∩ I i) = 0) :
    (∫ x in I i, (1 + direction μ (density μ H I q) x) ∂μ) =
      μ.real (I i) + ∫ x, q i x ∂μ.restrict H := by
  have hnot : ∀ᵐ x ∂μ, x ∉ H ∩ I i := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hHI
  have hsource (j : ℕ) : ∀ᵐ x ∂μ, x ∈ I i → liftFraction H q j x = 0 := by
    filter_upwards [hnot] with x hx hxi
    exact indicator_of_notMem (fun hxH => hx ⟨hxH, hxi⟩) _
  have h := AtomicAssignment.endpoint_mass_on_atom I hI (liftFraction H q)
    (integrable_lift H hH q) (fun j => nonnegative_lift H hH q j (hq0 j))
    (fun j h => zero_lift H hH q j (hzero j h)) (summable_lift H hH q hsum)
    hdisjoint i hsource
  rw [integral_lift H hH q i] at h
  exact h

/-- Original product-AE rectangle licenses and restricted source support
give actual support of the original product density, without a pair-AE upgrade. -/
theorem supported_density (H : Set Ω) (hH : MeasurableSet H)
    (I E : ℕ → Set Ω) (q : ℕ → Lp ℝ 2 (μ.restrict H)) (Z : Set (Ω × Ω))
    (hsupport : ∀ i, ∀ᵐ x ∂μ.restrict H, x ∉ E i → q i x = 0)
    (hrect : ∀ i, ∀ᵐ p ∂μ.prod μ, p.1 ∈ I i → p.2 ∈ H ∩ E i → p ∈ Z) :
    ∀ᵐ p ∂μ.prod μ, p ∉ Z → density μ H I q p = 0 := by
  apply AtomicAssignment.supported_density I (fun i => H ∩ E i) (liftFraction H q) Z
  · intro i
    filter_upwards [(ae_restrict_iff' hH).mp (hsupport i)] with x hx hnot
    by_cases hmem : x ∈ H
    · have hEi : x ∉ E i := fun hxE => hnot ⟨hmem, hxE⟩
      simpa only [liftFraction, indicator_of_mem hmem] using hx hmem hEi
    · exact indicator_of_notMem hmem _
  · exact hrect

end Erdos1017.MissingFlow.RestrictedAtomicAssignment
