module

public import Erdos1017.Exclusions.Common.FullCrossCompletionObstruction
public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomBlockGeometry

/-!
# Lower bound on the `E` star of a four-region optimum

Any represented active four-region full optimum has its `E` star above its own
`ell`, with the cross-completion geometry read off the block table and no
selected structure assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.TwoAtomCountGate

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- Any represented active four-region full optimum has its E star
above its own ell. The literal table supplies all cross-completion
geometry; no selected structure, new record, or star-floor hypothesis is used. -/
theorem v_gt_ell_of_fullStationaryClass (label : Ω → Fin 4) (hlabel : Measurable label)
    (hpos : ∀ i, 0 < μ (label ⁻¹' {i})) (x : Coefficients) (hx : ∀ i, 0 ≤ x i)
    (V : CappedModel.Model Ω μ) {d c m : ℝ} (hV : CappedModel.FullStationaryClass d c V m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hmom : ∀ p : Ω × Ω,
      V.moment CappedColor.adjacency p = (if blockAdjacency (label p.1) (label p.2) = true then 1 else 0) ∧
      V.moment CappedColor.charge p = blockCharge x (label p.1) (label p.2)) : -m < x 1 := by
  let R := label ⁻¹' {1}
  let C := label ⁻¹' {0}
  let F := label ⁻¹' {3}
  have hRC : Disjoint R C := by
    apply Set.disjoint_left.mpr
    intro z hzR hzC
    change label z = 1 at hzR
    change label z = 0 at hzC
    omega
  have hRF : Disjoint R F := by
    apply Set.disjoint_left.mpr
    intro z hzR hzF
    change label z = 1 at hzR
    change label z = 3 at hzF
    omega
  have hCF : Disjoint C F := by
    apply Set.disjoint_left.mpr
    intro z hzC hzF
    change label z = 0 at hzC
    change label z = 3 at hzF
    omega
  have hroot : ∀ᵐ p ∂μ.prod μ, p.1 ∈ R → p.2 ∈ R → CappedModel.adjacencyKernel V p.1 p.2 = 0 := by
    filter_upwards with p hp hq
    change V.moment CappedColor.adjacency p = 0
    change label p.1 = 1 at hp
    change label p.2 = 1 at hq
    rw [(hmom p).1, hp, hq]
    norm_num [blockAdjacency]
  have hcross : ∀ᵐ p ∂μ.prod μ, p.1 ∈ C → p.2 ∈ F → CappedModel.adjacencyKernel V p.1 p.2 = 0 := by
    filter_upwards with p hp hq
    change V.moment CappedColor.adjacency p = 0
    change label p.1 = 0 at hp
    change label p.2 = 3 at hq
    rw [(hmom p).1, hp, hq]
    norm_num [blockAdjacency]
  have hbody : ∀ᵐ p ∂μ.prod μ, p.1 ∉ R → p.2 ∉ R → CappedModel.chargeKernel V p.1 p.2 ≤ 0 := by
    filter_upwards with p hp hq
    change label p.1 ≠ 1 at hp
    change label p.2 ≠ 1 at hq
    change V.moment CappedColor.charge p ≤ 0
    rw [(hmom p).2]
    have hi : label p.1 = 0 ∨ label p.1 = 2 ∨ label p.1 = 3 := by omega
    have hj : label p.2 = 0 ∨ label p.2 = 2 ∨ label p.2 = 3 := by omega
    rcases hi with hi | hi | hi <;> rcases hj with hj | hj | hj <;>
      simp [blockCharge, hi, hj, hx]
  have hconstant : ∀ᵐ p ∂μ.prod μ, p.1 ∈ F → p.2 ∈ R → CappedModel.chargeKernel V p.1 p.2 = x 1 := by
    filter_upwards with p hp hq
    change label p.1 = 3 at hp
    change label p.2 = 1 at hq
    change V.moment CappedColor.charge p = x 1
    rw [(hmom p).2, hp, hq]
    norm_num [blockCharge]
  exact CappedModel.cross_root_charge_gt_of_constant V hV hd hgap R C F
    (hlabel (measurableSet_singleton 0)) (hlabel (measurableSet_singleton 3))
    (hpos 0) (hpos 3) hRC hRF hCF hroot hcross hbody hconstant

end Erdos1017.TwoAtomCountGate
