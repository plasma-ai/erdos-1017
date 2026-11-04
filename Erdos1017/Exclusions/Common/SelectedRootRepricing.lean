module

public import Erdos1017.Exclusions.Common.SelectedRootRows
public import Erdos1017.Exclusions.Common.SignedRootRepricingIntegrals

/-!
# Repricing a root atom

The internal degree `rootInternalDegree` of a chosen atom inside its
neighborhood is defined, every measurable root repricing has nonpositive
objective gain, and unsaturated root edges force at least the root mass in the
neighborhood degree, also for the original adjacency kernel.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ}

/-- Original degree inside the original neighborhood of the chosen atom. -/
def rootInternalDegree (S : SelectedHighLowStructure W m) (r : S.I) (x : Ω) : ℝ :=
  ∫ z in S.rootNeighborhood r,
    SignedRootRepricing.edgeWeight (PhysicalRepresentative.adjacency W m) x z ∂μ

omit [IsProbabilityMeasure μ] in
private theorem measurable_rootEdgeWeight :
    Measurable (Function.uncurry
      (SignedRootRepricing.edgeWeight (PhysicalRepresentative.adjacency W m))) :=
  Measurable.ite ((PhysicalRepresentative.measurable_adjacency W m)
    (measurableSet_singleton true)) measurable_const measurable_const

theorem measurable_rootInternalDegree (S : SelectedHighLowStructure W m) (r : S.I) :
    Measurable (S.rootInternalDegree r) :=
  measurable_rootEdgeWeight.stronglyMeasurable.integral_prod_right'.measurable

theorem rootInternalDegree_mem_Icc (S : SelectedHighLowStructure W m) (r : S.I) (x : Ω) :
    S.rootInternalDegree r x ∈ Icc (0 : ℝ) 1 := by
  let N := S.rootNeighborhood r
  let f := SignedRootRepricing.edgeWeight (PhysicalRepresentative.adjacency W m) x
  have hf : Measurable f := measurable_rootEdgeWeight.comp
    (measurable_const.prodMk measurable_id)
  have hb : ∀ y, f y ∈ Icc (0 : ℝ) 1 := by
    intro y
    unfold f SignedRootRepricing.edgeWeight
    split_ifs <;> constructor <;> norm_num
  have hi : Integrable f μ := Integrable.of_bound hf.aestronglyMeasurable 1
    (Eventually.of_forall (fun y => by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [(hb y).1], (hb y).2⟩))
  have hNi := hi.indicator (S.measurableSet_rootNeighborhood r)
  change (∫ y in N, f y ∂μ) ∈ Icc (0 : ℝ) 1
  rw [← integral_indicator (S.measurableSet_rootNeighborhood r)]
  constructor
  · apply integral_nonneg
    intro y
    change 0 ≤ N.indicator f y
    by_cases hy : y ∈ N <;> simp [hy, (hb y).1]
  · have hp : ∀ᵐ y ∂μ, N.indicator f y ≤ 1 := Eventually.of_forall (fun y => by
      by_cases hy : y ∈ N <;> simp [hy, (hb y).2])
    simpa using integral_mono_ae hNi (integrable_const (1 : ℝ)) hp

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- Every measurable root repricing has nonpositive original objective gain.
All scalar tests, row data and optimum comparisons are constructed from W. -/
theorem root_gain_nonpos (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (E : Set Ω) (hE : MeasurableSet E) :
    (∫ x in E ∩ S.rootNeighborhood r, (1 - S.rootChargeRow r x) *
      (μ.real {z | S.ρ z = r.val} - S.rootInternalDegree r x) ∂μ) ≤ 0 := by
  let I := {x | S.ρ x = r.val}
  let N := S.rootNeighborhood r
  let G := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  let h : Ω → ℝ := (E ∩ N).indicator (fun x => 1 - S.rootChargeRow r x)
  have hN : MeasurableSet N := S.measurableSet_rootNeighborhood r
  have hh : Measurable h := (measurable_const.sub (S.measurable_rootChargeRow r)).indicator
    (hE.inter hN)
  have hpos : ∀ x, 0 ≤ h x := by
    intro x
    by_cases hx : x ∈ E ∩ N
    · simp only [h, indicator_of_mem hx]
      linarith [(S.rootChargeRow_mem_Icc r x).2]
    · simp [h, hx]
  have hb : ∀ x, ‖h x‖ ≤ 4 := by
    intro x
    by_cases hx : x ∈ E ∩ N
    · simp only [h, indicator_of_mem hx, Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [(S.rootChargeRow_mem_Icc r x).2],
        by linarith [(S.rootChargeRow_mem_Icc r x).1]⟩
    · simp [h, hx]
  have hsupport : ∀ x ∉ N, h x = 0 := by
    intro x hx
    exact indicator_of_notMem (fun hi : x ∈ E ∩ N => hx hi.2) _
  have hcap : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → G p.1 p.2 = true →
      Y p.1 p.2 + h p.2 ≤ 1 := by
    filter_upwards [S.ae_root_charge r hW hd hgap] with p hp hi _
    change PhysicalRepresentative.charge W m p.1 p.2 + h p.2 ≤ 1
    by_cases hx : p.2 ∈ E ∩ N
    · rw [hp hi]
      simp [h, hx]
    · simpa [h, hx] using (PhysicalRepresentative.charge_mem_Icc W m p.1 p.2).2
  have hs := hW.strict_gap_structure hd hgap
  have hopt : FiniteCappedSamplingCost.physicalObjective μ Y =
      FractionalGraph.densityLimit (FiniteCappedSamplingCost.physicalDensity μ G) := by
    rw [PhysicalRepresentative.objective_eq W m hs.strict_support,
      PhysicalRepresentative.density_eq W m hs.strict_support, hW.objective_eq, hW.density_eq]
    exact hW.optimal
  have hgain := SignedRootRepricing.integral_gain_le_zero_of_full_optimum G
    (PhysicalRepresentative.adjacency_symm W m) (PhysicalRepresentative.measurable_adjacency W m)
    Y (PhysicalRepresentative.measurable_charge W m) 3 (by norm_num)
    (fun x y => by simpa only [Real.norm_eq_abs] using PhysicalRepresentative.charge_bound W m x y)
    (Eventually.of_forall (fun p => PhysicalRepresentative.charge_symm W m p.1 p.2))
    (Eventually.of_forall (fun p => (PhysicalRepresentative.charge_mem_Icc W m p.1 p.2).2))
    (Eventually.of_forall (fun p hp => PhysicalRepresentative.charge_zero_of_nonedge W m p.1 p.2 hp))
    (PhysicalRepresentative.full_feasible W hW.full m hs.strict_support hW.deterministic) hopt
    I N (S.hfibers r.val r.property).1 hN (S.rootNeighborhood_disjoint r)
    (S.ae_root_adjacency r hW hd hgap) h hh hpos hcap 4 (by norm_num) hb hsupport
  have heq : (fun x => h x * (μ.real I - S.rootInternalDegree r x)) =
      (E ∩ N).indicator (fun x => (1 - S.rootChargeRow r x) *
        (μ.real I - S.rootInternalDegree r x)) := by
    funext x
    by_cases hx : x ∈ E ∩ N <;> simp [h, hx]
  change (∫ x, h x * (μ.real I - S.rootInternalDegree r x) ∂μ) ≤ 0 at hgain
  rw [heq, integral_indicator (hE.inter hN)] at hgain
  exact hgain

/-- Unsaturated original root edges force at least the root mass in the
original neighborhood degree. The actual signed edit and localization are
derived for the same full optimum. -/
theorem ae_rootInternalDegree_ge_mass (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ x ∂μ, x ∈ S.rootNeighborhood r → S.rootChargeRow r x < 1 →
      μ.real {z | S.ρ z = r.val} ≤ S.rootInternalDegree r x := by
  let A := μ.real {z | S.ρ z = r.val}
  let N := S.rootNeighborhood r
  let f : Ω → ℝ := fun x => (1 - S.rootChargeRow r x) * (A - S.rootInternalDegree r x)
  let F := N.indicator f
  have hN : MeasurableSet N := S.measurableSet_rootNeighborhood r
  have hA0 : 0 ≤ A := ENNReal.toReal_nonneg
  have hA1 : A ≤ 1 := by
    simp [A]
  have hf : Measurable f := (measurable_const.sub (S.measurable_rootChargeRow r)).mul
    (measurable_const.sub (S.measurable_rootInternalDegree r))
  have hF : Measurable F := hf.indicator hN
  have hb : ∀ x, ‖F x‖ ≤ 4 := by
    intro x
    by_cases hx : x ∈ N
    · rw [show F x = f x from indicator_of_mem hx f]
      have hr := S.rootChargeRow_mem_Icc r x
      have hg := S.rootInternalDegree_mem_Icc r x
      have hfirst : ‖1 - S.rootChargeRow r x‖ ≤ 4 := by
        rw [Real.norm_eq_abs]
        exact abs_le.mpr ⟨by linarith [hr.2], by linarith [hr.1]⟩
      have hsecond : ‖A - S.rootInternalDegree r x‖ ≤ 1 := by
        rw [Real.norm_eq_abs]
        exact abs_le.mpr ⟨by linarith [hg.2], by linarith [hg.1]⟩
      change ‖(1 - S.rootChargeRow r x) * (A - S.rootInternalDegree r x)‖ ≤ 4
      rw [norm_mul]
      nlinarith [norm_nonneg (1 - S.rootChargeRow r x),
        norm_nonneg (A - S.rootInternalDegree r x)]
    · simp [F, hx]
  have hi : Integrable F μ := Integrable.of_bound hF.aestronglyMeasurable 4
    (Eventually.of_forall hb)
  have hnonpos : ∀ᵐ x ∂μ, F x ≤ 0 := by
    apply ae_le_of_forall_setIntegral_le hi (integrable_const (0 : ℝ))
    intro E hE _
    have hgain := S.root_gain_nonpos r hW hd hgap E hE
    change (∫ x in E, N.indicator f x ∂μ) ≤ ∫ _ in E, (0 : ℝ) ∂μ
    rw [integral_indicator hN, Measure.restrict_restrict hN]
    simpa only [integral_zero, Set.inter_comm] using hgain
  filter_upwards [hnonpos] with x hx hxN hy
  change N.indicator f x ≤ 0 at hx
  rw [indicator_of_mem hxN] at hx
  change (1 - S.rootChargeRow r x) * (A - S.rootInternalDegree r x) ≤ 0 at hx
  by_contra hbad
  have hgapDegree : 0 < A - S.rootInternalDegree r x := sub_pos.mpr (lt_of_not_ge hbad)
  exact (not_lt_of_ge hx) (mul_pos (sub_pos.mpr hy) hgapDegree)

/-- The neighborhood degree in the physical representative is the original
adjacency-kernel integral, under the original measure. -/
theorem ae_rootInternalDegree_eq_original (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ x ∂μ, S.rootInternalDegree r x =
      ∫ z in S.rootNeighborhood r, adjacencyKernel W x z ∂μ := by
  have hs := hW.strict_gap_structure hd hgap
  filter_upwards [Measure.ae_ae_of_ae_prod
    (PhysicalRepresentative.adjacency_moment_ae_eq W m hs.strict_support)] with x hx
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hx] with z hz
  exact hz.symm

/-- Original root repricing conclusion with the original adjacency kernel.
No geometry, edited model or local degree inequality is supplied. -/
theorem ae_original_root_degree_ge_mass (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ x ∂μ, x ∈ S.rootNeighborhood r → S.rootChargeRow r x < 1 →
      μ.real {z | S.ρ z = r.val} ≤
        ∫ z in S.rootNeighborhood r, adjacencyKernel W x z ∂μ := by
  filter_upwards [S.ae_rootInternalDegree_ge_mass r hW hd hgap,
    S.ae_rootInternalDegree_eq_original r hW hd hgap] with x hx heq hn hy
  rw [← heq]
  exact hx hn hy

end Erdos1017.CappedModel.SelectedHighLowStructure
