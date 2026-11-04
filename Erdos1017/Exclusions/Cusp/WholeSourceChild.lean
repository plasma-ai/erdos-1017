module

public import Erdos1017.Exclusions.Cusp.JoinedCellCollapse
public import Erdos1017.SelectedModel.Structure.IntegrableReweight
public import Erdos1017.SelectedModel.Flows.FlowClassMasses

/-!
# The whole-source child model

The child `weight` removes the original head, resets the peak and its whole
source remainder to mass `r`, and keeps the current outside law; its outside
square sum `outsideSquares` and retained off-J-square graph `outsideAdjacency`
are defined. A fully feasible multipartite child with its source cost bound is
constructed from the original model (`exists_child_with_cost`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.WholeSourceChild

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]

/-- The old head is removed, the peak and its whole source remainder are
reset to mass r, and the current outside law is retained. -/
def weight (P I J : Set Ω) (r a z : ℝ) (x : Ω) : ℝ :=
  if x ∈ P then 0 else if x ∈ I then r / a else if x ∈ J then r / z else 1

theorem measurable_weight (P I J : Set Ω) (hP : MeasurableSet P)
    (hI : MeasurableSet I) (hJ : MeasurableSet J) (r a z : ℝ) :
    Measurable (weight P I J r a z) :=
  Measurable.ite hP measurable_const
    (Measurable.ite hI measurable_const (Measurable.ite hJ measurable_const measurable_const))

theorem integrable_weight (P I J : Set Ω) (hP : MeasurableSet P)
    (hI : MeasurableSet I) (hJ : MeasurableSet J) (r a z : ℝ) :
    Integrable (weight P I J r a z) ν := by
  apply Integrable.of_bound (measurable_weight P I J hP hI hJ r a z).aestronglyMeasurable
    (|r / a| + |r / z| + 1)
  apply Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs]
  unfold weight
  split_ifs
  · simp only [abs_zero]
    positivity
  · linarith [abs_nonneg (r / z)]
  · linarith [abs_nonneg (r / a)]
  · simp only [abs_one]
    linarith [abs_nonneg (r / a), abs_nonneg (r / z)]

omit [MeasurableSpace Ω] [IsProbabilityMeasure ν] in
theorem weight_nonnegative (P I J : Set Ω) {r a z : ℝ}
    (hr : 0 ≤ r) (ha : 0 ≤ a) (hz : 0 ≤ z) (x : Ω) :
    0 ≤ weight P I J r a z x := by
  unfold weight
  split_ifs
  · exact le_rfl
  · exact div_nonneg hr ha
  · exact div_nonneg hr hz
  · norm_num

omit [MeasurableSpace Ω] [IsProbabilityMeasure ν] in
theorem weight_eq_indicators (P I J : Set Ω) (hPI : Disjoint P I)
    (hPJ : Disjoint P J) (hIJ : Disjoint I J) (r a z : ℝ) (x : Ω) :
    weight P I J r a z x = 1 - P.indicator (fun _ => (1 : ℝ)) x +
      (r / a - 1) * I.indicator (fun _ => (1 : ℝ)) x +
      (r / z - 1) * J.indicator (fun _ => (1 : ℝ)) x := by
  by_cases hp : x ∈ P
  · have hi : x ∉ I := fun hx => Set.disjoint_left.mp hPI hp hx
    have hj : x ∉ J := fun hx => Set.disjoint_left.mp hPJ hp hx
    simp [weight, hp, hi, hj]
  · by_cases hi : x ∈ I
    · have hj : x ∉ J := fun hx => Set.disjoint_left.mp hIJ hi hx
      simp [weight, hp, hi, hj]
    · by_cases hj : x ∈ J <;> simp [weight, hp, hi, hj]

/-- This is the actual probability normalization, including a deleted head. -/
theorem integral_weight (P I J : Set Ω) (hP : MeasurableSet P)
    (hI : MeasurableSet I) (hJ : MeasurableSet J)
    (hPI : Disjoint P I) (hPJ : Disjoint P J) (hIJ : Disjoint I J)
    (ha : 0 < ν.real I) (hz : 0 < ν.real J) :
    (∫ x, weight P I J ((ν.real P + ν.real I + ν.real J) / 2) (ν.real I) (ν.real J) x ∂ν) = 1 := by
  simp_rw [weight_eq_indicators P I J hPI hPJ hIJ]
  rw [integral_add, integral_add, integral_sub]
  · rw [integral_const_mul, integral_const_mul,
      integral_indicator hP, integral_indicator hI, integral_indicator hJ]
    simp only [integral_const, probReal_univ, measureReal_restrict_apply_univ, smul_eq_mul, mul_one]
    field_simp [ha.ne', hz.ne']
    ring
  · exact integrable_const 1
  · exact (integrable_const 1).indicator hP
  · exact ((integrable_const 1).sub ((integrable_const 1).indicator hP))
  · exact ((integrable_const 1).indicator hI).const_mul _
  · exact ((integrable_const 1).sub ((integrable_const 1).indicator hP)).add
      (((integrable_const 1).indicator hI).const_mul _)
  · exact ((integrable_const 1).indicator hJ).const_mul _

/-- Every measurable old cell on which the literal weight is constant has
its exact changed mass, without a mass-retention assumption. -/
theorem weighted_real_set (P I J : Set Ω) (hP : MeasurableSet P)
    (hI : MeasurableSet I) (hJ : MeasurableSet J) {r a z : ℝ}
    (hr : 0 ≤ r) (ha : 0 ≤ a) (hz : 0 ≤ z)
    (C : Set Ω) (hC : MeasurableSet C) (k : ℝ)
    (hk : ∀ x ∈ C, weight P I J r a z x = k) :
    (weightedMeasure (μ := ν) (weight P I J r a z)).real C = k * ν.real C := by
  rw [weightedMeasure_real_set _ (integrable_weight P I J hP hI hJ r a z)
    (Eventually.of_forall (weight_nonnegative P I J hr ha hz)) C hC]
  calc
    _ = ∫ _ in C, k ∂ν := integral_congr_ae ((ae_restrict_mem hC).mono hk)
    _ = k * ν.real C := by rw [setIntegral_const, smul_eq_mul, mul_comm]

/-- Both retained child heads have this common current-law mass. -/
def halfMass (ν : Measure Ω) (P I J : Set Ω) : ℝ :=
  (ν.real P + ν.real I + ν.real J) / 2

/-- The child's actual probability law permits the old head to vanish. -/
def law (ν : Measure Ω) (P I J : Set Ω) : Measure Ω :=
  weightedMeasure (μ := ν) (weight P I J (halfMass ν P I J) (ν.real I) (ν.real J))

omit [IsProbabilityMeasure ν] in
theorem halfMass_pos (P I J : Set Ω) (ha : 0 < ν.real I) (hz : 0 < ν.real J) :
    0 < halfMass ν P I J := by
  unfold halfMass
  linarith [measureReal_nonneg (μ := ν) (s := P)]

theorem law_probability (P I J : Set Ω) (hP : MeasurableSet P)
    (hI : MeasurableSet I) (hJ : MeasurableSet J)
    (hPI : Disjoint P I) (hPJ : Disjoint P J) (hIJ : Disjoint I J)
    (ha : 0 < ν.real I) (hz : 0 < ν.real J) : IsProbabilityMeasure (law ν P I J) :=
  weightedMeasure_probability (integrable_weight P I J hP hI hJ _ _ _)
    (Eventually.of_forall (weight_nonnegative P I J (halfMass_pos P I J ha hz).le ha.le hz.le))
    (integral_weight P I J hP hI hJ hPI hPJ hIJ ha hz)

theorem law_head_mass (P I J : Set Ω) (hP : MeasurableSet P)
    (hI : MeasurableSet I) (hJ : MeasurableSet J)
    (ha : 0 < ν.real I) (hz : 0 < ν.real J) : (law ν P I J).real P = 0 := by
  rw [law, weighted_real_set P I J hP hI hJ (halfMass_pos P I J ha hz).le ha.le hz.le
    P hP 0 (fun x hx => by simp only [weight, hx, ↓reduceIte]), zero_mul]

theorem law_peak_mass (P I J : Set Ω) (hP : MeasurableSet P)
    (hI : MeasurableSet I) (hJ : MeasurableSet J) (hPI : Disjoint P I)
    (ha : 0 < ν.real I) (hz : 0 < ν.real J) :
    (law ν P I J).real I = halfMass ν P I J := by
  rw [law, weighted_real_set P I J hP hI hJ (halfMass_pos P I J ha hz).le ha.le hz.le
    I hI (halfMass ν P I J / ν.real I) (fun x hx => by
      have hp : x ∉ P := fun hp => Set.disjoint_left.mp hPI hp hx
      simp only [weight, hp, hx, ↓reduceIte]), div_mul_cancel₀ _ ha.ne']

theorem law_source_mass (P I J : Set Ω) (hP : MeasurableSet P)
    (hI : MeasurableSet I) (hJ : MeasurableSet J)
    (hPJ : Disjoint P J) (hIJ : Disjoint I J)
    (ha : 0 < ν.real I) (hz : 0 < ν.real J) :
    (law ν P I J).real J = halfMass ν P I J := by
  rw [law, weighted_real_set P I J hP hI hJ (halfMass_pos P I J ha hz).le ha.le hz.le
    J hJ (halfMass ν P I J / ν.real J) (fun x hx => by
      have hp : x ∉ P := fun hp => Set.disjoint_left.mp hPJ hp hx
      have hi : x ∉ I := fun hi => Set.disjoint_left.mp hIJ hi hx
      simp only [weight, hp, hi, hx, ↓reduceIte]), div_mul_cancel₀ _ hz.ne']

/-- Every literal outside cell retains its current mass. -/
theorem law_outside_mass (P I J : Set Ω) (hP : MeasurableSet P)
    (hI : MeasurableSet I) (hJ : MeasurableSet J)
    (ha : 0 < ν.real I) (hz : 0 < ν.real J)
    (C : Set Ω) (hC : MeasurableSet C) (hCP : Disjoint C P)
    (hCI : Disjoint C I) (hCJ : Disjoint C J) : (law ν P I J).real C = ν.real C := by
  rw [law, weighted_real_set P I J hP hI hJ (halfMass_pos P I J ha hz).le ha.le hz.le
    C hC 1 (fun x hx => by
      have hp : x ∉ P := fun hp => Set.disjoint_left.mp hCP hx hp
      have hi : x ∉ I := fun hi => Set.disjoint_left.mp hCI hx hi
      have hj : x ∉ J := fun hj => Set.disjoint_left.mp hCJ hx hj
      simp only [weight, hp, hi, hj, ↓reduceIte]), one_mul]

/-- The actual changed-law full model is collapsed only after the old
head has genuinely acquired measure zero. -/
theorem exists_child (W : Model Ω ν) (hW : FullFeasible W)
    (A : Ω → Ω → Bool) (hA : Measurable (Function.uncurry A))
    (hAsym : ∀ x y, A x y = A y x)
    (hAdj : ∀ᵐ p ∂ν.prod ν, W.moment CappedColor.adjacency p =
      if A p.1 p.2 = true then 1 else 0)
    (P I J : Set Ω) (hP : MeasurableSet P) (hI : MeasurableSet I) (hJ : MeasurableSet J)
    (hPI : Disjoint P I) (hPJ : Disjoint P J) (hIJ : Disjoint I J)
    (ha : 0 < ν.real I) (hz : 0 < ν.real J)
    (hjoin : ∀ᵐ p ∂ν.prod ν, p.1 ∈ J → p.2 ∉ J → p.2 ∉ P →
      A p.1 p.2 = true ∧ A p.2 p.1 = true) :
    ∃ V : Model Ω (law ν P I J), FullFeasible V ∧
      (∀ p, V.moment CappedColor.adjacency p =
        if JoinedCellCollapse.adjacency A J p.1 p.2 = true then 1 else 0) ∧
      (∀ᵐ p ∂(law ν P I J).prod (law ν P I J), V.moment CappedColor.charge p =
        MultipartiteDustAtomization.atomizedCharge (ν := law ν P I J) J
          (fun p => chargeKernel W p.1 p.2) p) ∧
      objective V = KernelOperator.kernelEnergy (μ := ν) (chargeKernel W)
        (weight P I J (halfMass ν P I J) (ν.real I) (ν.real J)) / 2 -
          (∫ p in J ×ˢ J, chargeKernel W p.1 p.2 ∂(law ν P I J).prod (law ν P I J)) / 2 := by
  let w := weight P I J (halfMass ν P I J) (ν.real I) (ν.real J)
  have hw : Integrable w ν := integrable_weight P I J hP hI hJ _ _ _
  have hw0 : ∀ᵐ x ∂ν, 0 ≤ w x :=
    Eventually.of_forall (weight_nonnegative P I J (halfMass_pos P I J ha hz).le ha.le hz.le)
  have hw1 : (∫ x, w x ∂ν) = 1 := integral_weight P I J hP hI hJ hPI hPJ hIJ ha hz
  let ν' := law ν P I J
  have : IsProbabilityMeasure ν' := law_probability P I J hP hI hJ hPI hPJ hIJ ha hz
  have hac : ν' ≪ ν := withDensity_absolutelyContinuous _ _
  have hac2 := hac.prod hac
  have hPnull : ν' P = 0 := by
    apply (measureReal_eq_zero_iff (measure_ne_top ν' P)).mp
    exact law_head_mass P I J hP hI hJ ha hz
  have hoffP : ∀ᵐ x ∂ν', x ∉ P := by
    rw [ae_iff]
    have he : {x | ¬x ∉ P} = P := by ext x; simp
    rw [he]
    exact hPnull
  have hjoin' : ∀ᵐ p ∂ν'.prod ν', p.1 ∈ J → p.2 ∉ J →
      A p.1 p.2 = true ∧ A p.2 p.1 = true := by
    filter_upwards [hac2.ae_le hjoin, Measure.quasiMeasurePreserving_snd.ae hoffP]
      with p hp hnot h₁ h₂
    exact hp h₁ h₂ hnot
  have hJpos : 0 < ν' J := by
    have hr : 0 < ν'.real J := by
      rw [law_source_mass P I J hP hI hJ hPJ hIJ ha hz]
      exact halfMass_pos P I J ha hz
    exact (ENNReal.toReal_pos_iff.mp hr).1
  have : IsProbabilityMeasure (weightedMeasure (μ := ν) w) := weightedMeasure_probability hw hw0 hw1
  let U := integrableReweight W w hw hw0 hw1
  obtain ⟨V, hV, hVA, hVY, _, hVc⟩ := JoinedCellCollapse.exists_model U
    (fullFeasible_integrableReweight W hW w hw hw0 hw1) A hA hAsym
    (hac2.ae_le hAdj) J hJ hJpos hjoin'
  refine ⟨V, hV, hVA, hVY, ?_⟩
  change objective V = KernelOperator.kernelEnergy (μ := ν) (chargeKernel W) w / 2 -
    (∫ p in J ×ˢ J, chargeKernel U p.1 p.2 ∂(weightedMeasure (μ := ν) w).prod
      (weightedMeasure (μ := ν) w)) / 2
  rw [hVc, objective_integrableReweight W w hw hw0 hw1]

section MultipartiteSupport

variable {ι : Type*} [Countable ι]

local instance childOptionMeasurable : MeasurableSpace (Option ι) := ⊤
local instance childNewOptionMeasurable : MeasurableSpace (Option (Bool ⊕ ι)) := ⊤

/-- The two equal child heads are literal independent classes; none
continues to denote genuine clique dust in the current outside law. -/
def labels (q : Ω → Option ι) (I J : Set Ω) (x : Ω) : Option (Bool ⊕ ι) :=
  if x ∈ I then some (.inl true) else if x ∈ J then some (.inl false) else (q x).map Sum.inr

theorem measurable_labels (q : Ω → Option ι) (hq : Measurable q)
    (I J : Set Ω) (hI : MeasurableSet I) (hJ : MeasurableSet J) :
    Measurable (labels q I J) :=
  Measurable.ite hI measurable_const (Measurable.ite hJ measurable_const
    ((measurable_of_countable (Option.map Sum.inr)).comp hq))

omit [Countable ι] [MeasurableSpace Ω] [IsProbabilityMeasure ν] in
theorem labels_peak_fiber (q : Ω → Option ι) (I J : Set Ω) :
    labels q I J ⁻¹' {some (.inl true)} = I := by
  ext x
  by_cases hi : x ∈ I <;> by_cases hj : x ∈ J <;> cases hq : q x <;>
    simp [labels, hi, hj, hq]

omit [Countable ι] [MeasurableSpace Ω] [IsProbabilityMeasure ν] in
theorem labels_source_fiber (q : Ω → Option ι) (I J : Set Ω) (hIJ : Disjoint I J) :
    labels q I J ⁻¹' {some (.inl false)} = J := by
  ext x
  by_cases hi : x ∈ I
  · have hj : x ∉ J := fun hj => Set.disjoint_left.mp hIJ hi hj
    simp [labels, hi, hj]
  · by_cases hj : x ∈ J <;> cases hq : q x <;> simp [labels, hi, hj, hq]

omit [Countable ι] [MeasurableSpace Ω] [IsProbabilityMeasure ν] in
theorem labels_outside_fiber (q : Ω → Option ι) (I J : Set Ω) (i : ι) :
    labels q I J ⁻¹' {some (.inr i)} = (q ⁻¹' {some i}) \ (I ∪ J) := by
  ext x
  by_cases hi : x ∈ I <;> by_cases hj : x ∈ J <;> cases hq : q x <;>
    simp [labels, hi, hj, hq]

/-- Only the displayed current outside classes contribute to the tail. -/
def outsideClass (q : Ω → Option ι) (P I J : Set Ω) (i : ι) : Set Ω :=
  (q ⁻¹' {some i}) \ (P ∪ I ∪ J)

theorem measurable_outsideClass (q : Ω → Option ι) (hq : Measurable q)
    (P I J : Set Ω) (hP : MeasurableSet P) (hI : MeasurableSet I)
    (hJ : MeasurableSet J) (i : ι) : MeasurableSet (outsideClass q P I J i) :=
  (hq (measurableSet_singleton (some i))).diff ((hP.union hI).union hJ)

theorem law_outside_class_mass (q : Ω → Option ι) (hq : Measurable q)
    (P I J : Set Ω) (hP : MeasurableSet P) (hI : MeasurableSet I) (hJ : MeasurableSet J)
    (hPI : Disjoint P I) (hPJ : Disjoint P J) (hIJ : Disjoint I J)
    (ha : 0 < ν.real I) (hz : 0 < ν.real J) (i : ι) :
    MultipartiteClassMasses.classMass (law ν P I J) (labels q I J) (.inr i) =
      ν.real (outsideClass q P I J i) := by
  let := law_probability P I J hP hI hJ hPI hPJ hIJ ha hz
  rw [MultipartiteClassMasses.classMass, labels_outside_fiber]
  have he : ((q ⁻¹' {some i}) \ (I ∪ J)) \ P = outsideClass q P I J i := by
    ext x
    simp only [outsideClass, Set.mem_sdiff, mem_union]
    tauto
  rw [← measureReal_sdiff_null (s₁ := (q ⁻¹' {some i}) \ (I ∪ J))
    (law_head_mass P I J hP hI hJ ha hz), he]
  apply law_outside_mass P I J hP hI hJ ha hz _
    (measurable_outsideClass q hq P I J hP hI hJ i)
  all_goals
    apply Set.disjoint_left.mpr
    intro x hx hy
    simp only [outsideClass, Set.mem_sdiff, mem_union] at hx
    tauto

theorem outside_square_summable (q : Ω → Option ι) (hq : Measurable q)
    (P I J : Set Ω) : Summable (fun i => (ν.real (outsideClass q P I J i)) ^ 2) := by
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun i => ?_) (MultipartiteClassMasses.classMass_sq_summable (μ := ν) q hq)
  apply pow_le_pow_left₀ ENNReal.toReal_nonneg
  exact measureReal_mono sdiff_subset

/-- This is the source's actual current outside square sum QO. -/
def outsideSquares (ν : Measure Ω) (q : Ω → Option ι) (P I J : Set Ω) : ℝ :=
  ∑' i, (ν.real (outsideClass q P I J i)) ^ 2

omit [Countable ι] [MeasurableSpace Ω] [IsProbabilityMeasure ν] in
/-- The concrete old off-J-square graph retained by the source child. -/
def outsideAdjacency (q : Ω → Option ι) (I J : Set Ω) (x y : Ω) : Bool :=
  if x ∈ I ∧ y ∈ I then false else
    if x ∈ I ∨ y ∈ I ∨ x ∈ J ∨ y ∈ J then true else
      MultipartiteDustAtomization.adjacency q x y

omit [Countable ι] [MeasurableSpace Ω] [IsProbabilityMeasure ν] in
theorem collapsed_adjacency_labels (A : Ω → Ω → Bool) (q : Ω → Option ι)
    (I J : Set Ω) (hIJ : Disjoint I J) (x y : Ω)
    (hA : (x ∉ J ∨ y ∉ J) → A x y = outsideAdjacency q I J x y) :
    JoinedCellCollapse.adjacency A J x y =
      MultipartiteDustAtomization.adjacency (labels q I J) x y := by
  have hdisj (z : Ω) : ¬(z ∈ I ∧ z ∈ J) := fun hz => Set.disjoint_left.mp hIJ hz.1 hz.2
  by_cases hi : x ∈ I <;> by_cases hj : x ∈ J <;>
    by_cases hiy : y ∈ I <;> by_cases hjy : y ∈ J
  all_goals try exact False.elim (hdisj x ⟨hi, hj⟩)
  all_goals try exact False.elim (hdisj y ⟨hiy, hjy⟩)
  all_goals try simp only [JoinedCellCollapse.adjacency, hj, hjy, and_self, ↓reduceIte,
    MultipartiteDustAtomization.adjacency, labels, hi, hiy]
  all_goals try rw [hA (by tauto)]
  all_goals cases hqx : q x <;> cases hqy : q y <;>
    simp [outsideAdjacency, MultipartiteDustAtomization.adjacency, hi, hj, hiy, hjy,
      hqx, hqy]

variable [StandardBorelSpace Ω] [NullSingletonClass ν]

/-- The actual current outside profile and its two equal heads give the
source bound, after deriving the child's multipartite support and masses. -/
theorem objective_le_max_square
    (A : Ω → Ω → Bool) (q : Ω → Option ι) (hq : Measurable q)
    (P I J : Set Ω) (hP : MeasurableSet P) (hI : MeasurableSet I) (hJ : MeasurableSet J)
    (hPI : Disjoint P I) (hPJ : Disjoint P J) (hIJ : Disjoint I J)
    (ha : 0 < ν.real I) (hz : 0 < ν.real J)
    (hblock : ∀ᵐ p ∂ν.prod ν, p.1 ∉ P → p.2 ∉ P → (p.1 ∉ J ∨ p.2 ∉ J) →
      A p.1 p.2 = outsideAdjacency q I J p.1 p.2)
    (V : Model Ω (law ν P I J)) (hV : FullFeasible V)
    (hVA : ∀ p, V.moment CappedColor.adjacency p =
      if JoinedCellCollapse.adjacency A J p.1 p.2 = true then 1 else 0) :
    objective V ≤ max ((halfMass ν P I J) ^ 2) (outsideSquares ν q P I J) := by
  let ν' := law ν P I J
  let := law_probability P I J hP hI hJ hPI hPJ hIJ ha hz
  let : NullSingletonClass ν' := by
    change NullSingletonClass (ν.withDensity _)
    infer_instance
  have hac : ν' ≪ ν := withDensity_absolutelyContinuous _ _
  have hoffP : ∀ᵐ x ∂ν', x ∉ P := by
    rw [ae_iff]
    have he : {x | ¬x ∉ P} = P := by ext x; simp
    rw [he]
    exact (measureReal_eq_zero_iff (measure_ne_top ν' P)).mp
      (law_head_mass P I J hP hI hJ ha hz)
  have hs : ∀ᵐ p ∂ν'.prod ν', V.moment CappedColor.adjacency p =
      if labels q I J p.1 ≠ labels q I J p.2 ∨ labels q I J p.1 = none then 1 else 0 := by
    filter_upwards [(hac.prod hac).ae_le hblock,
      Measure.quasiMeasurePreserving_fst.ae hoffP,
      Measure.quasiMeasurePreserving_snd.ae hoffP] with p hp hx hy
    rw [hVA p, collapsed_adjacency_labels A q I J hIJ p.1 p.2 (hp hx hy)]
    simp only [MultipartiteDustAtomization.adjacency]
    by_cases h : labels q I J p.1 ≠ labels q I J p.2 ∨ labels q I J p.1 = none <;> simp [h]
  let M := max ((halfMass ν P I J) ^ 2) (outsideSquares ν q P I J)
  have hM : 0 ≤ M := (sq_nonneg _).trans (le_max_left _ _)
  have hheads : halfMass ν P I J ≤ Real.sqrt M := by
    apply (sq_le_sq₀ (halfMass_pos P I J ha hz).le (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hM]
    exact le_max_left _ _
  have hclasses : ∀ i, MultipartiteClassMasses.classMass ν' (labels q I J) i ≤ Real.sqrt M := by
    intro i
    cases i with
    | inl b =>
      cases b
      · simp only [MultipartiteClassMasses.classMass, labels_source_fiber q I J hIJ]
        change (law ν P I J).real J ≤ _
        rw [law_source_mass P I J hP hI hJ hPJ hIJ ha hz]
        exact hheads
      · simp only [MultipartiteClassMasses.classMass, labels_peak_fiber q I J]
        change (law ν P I J).real I ≤ _
        rw [law_peak_mass P I J hP hI hJ hPI ha hz]
        exact hheads
    | inr i =>
      rw [law_outside_class_mass q hq P I J hP hI hJ hPI hPJ hIJ ha hz i]
      apply (sq_le_sq₀ ENNReal.toReal_nonneg (Real.sqrt_nonneg _)).mp
      rw [Real.sq_sqrt hM]
      exact ((outside_square_summable q hq P I J).le_tsum i (fun _ _ => sq_nonneg _)).trans
        (le_max_right _ _)
  have h := MultipartiteClassMasses.objective_le_class_bound_sq V hV (labels q I J)
    (measurable_labels q hq I J hI hJ) (by
      filter_upwards [hs] with p hp
      split_ifs at hp ⊢ <;> exact hp) (Real.sqrt M) hclasses
  rwa [Real.sq_sqrt hM] at h

/-- A genuine full-feasible multipartite child and its source cost bound
are constructed from the old model and concrete retained outside graph. -/
theorem exists_child_with_cost (W : Model Ω ν) (hW : FullFeasible W)
    (A : Ω → Ω → Bool) (hA : Measurable (Function.uncurry A))
    (hAsym : ∀ x y, A x y = A y x)
    (hAdj : ∀ᵐ p ∂ν.prod ν, W.moment CappedColor.adjacency p =
      if A p.1 p.2 = true then 1 else 0)
    (q : Ω → Option ι) (hq : Measurable q)
    (P I J : Set Ω) (hP : MeasurableSet P) (hI : MeasurableSet I) (hJ : MeasurableSet J)
    (hPI : Disjoint P I) (hPJ : Disjoint P J) (hIJ : Disjoint I J)
    (ha : 0 < ν.real I) (hz : 0 < ν.real J)
    (hjoin : ∀ᵐ p ∂ν.prod ν, p.1 ∈ J → p.2 ∉ J → p.2 ∉ P →
      A p.1 p.2 = true ∧ A p.2 p.1 = true)
    (hblock : ∀ᵐ p ∂ν.prod ν, p.1 ∉ P → p.2 ∉ P → (p.1 ∉ J ∨ p.2 ∉ J) →
      A p.1 p.2 = outsideAdjacency q I J p.1 p.2) :
    ∃ V : Model Ω (law ν P I J), FullFeasible V ∧
      (∀ p, V.moment CappedColor.adjacency p =
        if JoinedCellCollapse.adjacency A J p.1 p.2 = true then 1 else 0) ∧
      objective V = KernelOperator.kernelEnergy (μ := ν) (chargeKernel W)
        (weight P I J (halfMass ν P I J) (ν.real I) (ν.real J)) / 2 -
          (∫ p in J ×ˢ J, chargeKernel W p.1 p.2 ∂(law ν P I J).prod (law ν P I J)) / 2 ∧
      objective V ≤ max ((halfMass ν P I J) ^ 2) (outsideSquares ν q P I J) := by
  obtain ⟨V, hV, hVA, _, hVc⟩ := exists_child W hW A hA hAsym hAdj P I J hP hI hJ
    hPI hPJ hIJ ha hz hjoin
  exact ⟨V, hV, hVA, hVc, objective_le_max_square A q hq P I J hP hI hJ hPI hPJ hIJ ha hz
    hblock V hV hVA⟩

end MultipartiteSupport

end Erdos1017.CappedModel.WholeSourceChild
