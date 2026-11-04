module

public import Erdos1017.Exclusions.Common.ConditionalRootedCounts
public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredCopyBonuses
public import Erdos1017.Exclusions.Common.SelectedDiffuseIncidence

/-!
# Conditional rooted counts of the zero-body optimum

The conditional coefficients of the zero-body optimum on two positive diffuse
regions are nonnegative and satisfy every rooted count, the saturated head
splits `D` into neighborhood and complement, and the three conditional diffuse
penalties keep the gamma bound and exceed half of delta under an explicit
contact ratio.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem region_average_nonnegative
    (Y : Ω → Ω → ℝ) (T : Fin 3 → Set Ω) (hT : ∀ i, MeasurableSet (T i))
    (i j : Fin 3)
    (h : ∀ᵐ p ∂μ.prod μ, p.1 ∈ T i → p.2 ∈ T j → 0 ≤ Y p.1 p.2) :
    0 ≤ FiniteArity.regionPairCharge μ Y T i j := by
  apply integral_nonneg_of_ae
  have hac : (cond μ (T i)).prod (cond μ (T j)) ≪ μ.prod μ :=
    cond_absolutelyContinuous.prod cond_absolutelyContinuous
  filter_upwards [hac.ae_le h,
    Measure.quasiMeasurePreserving_fst.ae (ae_cond_mem (hT i)),
    Measure.quasiMeasurePreserving_snd.ae (ae_cond_mem (hT j))] with p hp hi hj
  exact hp hi hj

/-- Actual conditional coefficients on any two positive diffuse regions
are nonnegative and satisfy every rooted count. Both facts are derived
from the same zero-body optimum, not an averaged-model certificate. -/
theorem conditional_rooted_coefficients_of_zero_body
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (R E : Set Ω) (hR : MeasurableSet R) (hE : MeasurableSet E)
    (hRpos : 0 < μ R) (hEpos : 0 < μ E) (hRD : R ⊆ S.D) (hED : E ⊆ S.D) :
    let x := FiniteArity.rootedRegionCoefficients μ (PhysicalRepresentative.charge W m)
      ![{x | S.ρ x = r.val}, R, E]
    (∀ i, 0 ≤ x i) ∧ ∀ k l : ℕ,
      x 0 * k + x 1 * l - x 2 * k * ((k : ℝ) - 1) / 2 -
        x 3 * l * ((l : ℝ) - 1) / 2 - x 4 * k * l ≤ 1 := by
  let T : Fin 3 → Set Ω := ![{x | S.ρ x = r.val}, R, E]
  let A := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  have hT : ∀ i, MeasurableSet (T i) := by
    intro i
    fin_cases i
    · exact (S.hfibers r.val r.property).1
    · exact hR
    · exact hE
  have hpos : ∀ i, 0 < μ (T i) := by
    intro i
    fin_cases i
    · exact (S.hfibers r.val r.property).2.1
    · exact hRpos
    · exact hEpos
  have hTD : ∀ i, i ≠ 0 → T i ⊆ S.D := by
    intro i hi
    fin_cases i
    · exact False.elim (hi rfl)
    · exact hRD
    · exact hED
  have hs := hW.strict_gap_structure hd hgap
  have hu := S.ae_root_universal_of_zero_body r hW hd hgap hzero
  have hus := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hu
  have hDD : ∀ᵐ p ∂μ.prod μ, p.1 ∈ S.D → p.2 ∈ S.D → A p.1 p.2 = true := by
    filter_upwards [S.hDcomplete,
      PhysicalRepresentative.adjacency_moment_ae_eq W m hs.strict_support] with p hc hm hx hy
    have hG := hc hx hy
    cases he : PhysicalRepresentative.adjacency W m p.1 p.2 <;> simp_all [A]
  have hclique : ∀ i j : Fin 3, (i ≠ 0 ∨ j ≠ 0) → ∀ᵐ p ∂μ.prod μ,
      p.1 ∈ T i → p.2 ∈ T j → A p.1 p.2 = true := by
    intro i j hij
    filter_upwards [hu, hus, hDD] with p hu hs hd hx hy
    by_cases hi : i = 0
    · have hj : j ≠ 0 := by simpa [hi] using hij
      have hxR : S.ρ p.1 = r.val := by simpa [hi, T] using hx
      exact (hu hxR).mpr (S.row_ne_atom_of_mem_diffuse p.2 (hTD j hj hy) r)
    · by_cases hj : j = 0
      · have hyR : S.ρ p.2 = r.val := by simpa [hj, T] using hy
        exact (PhysicalRepresentative.adjacency_symm W m p.1 p.2).trans
          ((hs hyR).mpr (S.row_ne_atom_of_mem_diffuse p.1 (hTD i hi hx) r))
      · exact hd (hTD i hi hx) (hTD j hj hy)
  have hstar : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → p.2 ∈ S.D → 0 ≤ Y p.1 p.2 := by
    filter_upwards [S.ae_root_charge r hW hd hgap,
      Measure.quasiMeasurePreserving_snd.ae (S.ae_rootChargeRow_pos_of_zero_body r hW hd hgap hzero)]
      with p hp ht hx hy
    exact (hp hx).trans_ge (ht (S.row_ne_atom_of_mem_diffuse p.2 hy r)).le
  have hbody : ∀ᵐ p ∂μ.prod μ, p.1 ∈ S.D → p.2 ∈ S.D → Y p.1 p.2 ≤ 0 := by
    filter_upwards [S.zero_body_ae_charge_nonpositive r hzero,
      PhysicalRepresentative.charge_ae_eq W m hs.strict_support] with p hb he hx hy
    exact he.trans_le (hb (S.row_ne_atom_of_mem_diffuse p.1 hx r)
      (S.row_ne_atom_of_mem_diffuse p.2 hy r))
  have hroot (j : Fin 3) (hj : j ≠ 0) : 0 ≤ FiniteArity.regionPairCharge μ Y T 0 j :=
    region_average_nonnegative Y T hT 0 j (hstar.mono (fun p hp hx hy => hp hx (hTD j hj hy)))
  have hpenalty (i j : Fin 3) (hi : i ≠ 0) (hj : j ≠ 0) :
      0 ≤ -FiniteArity.regionPairCharge μ Y T i j := by
    have hneg := region_average_nonnegative (fun x y => -Y x y) T hT i j
      (hbody.mono (fun p hp hx hy => neg_nonneg.mpr (hp (hTD i hi hx) (hTD j hj hy))))
    simpa only [FiniteArity.regionPairCharge, integral_neg] using hneg
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases i
    · exact hroot 1 (by decide)
    · exact hroot 2 (by decide)
    · exact hpenalty 1 1 (by decide) (by decide)
    · exact hpenalty 2 2 (by decide) (by decide)
    · exact hpenalty 1 2 (by decide) (by decide)
  · exact FiniteArity.rooted_region_count_le_one μ T hT hpos A Y
      (PhysicalRepresentative.measurable_charge W m) (PhysicalRepresentative.charge_symm W m)
      3 (PhysicalRepresentative.charge_bound W m)
      (PhysicalRepresentative.full_feasible W hW.full m hs.strict_support hW.deterministic) hclique

/-- The actual saturated-head split D intersect N(a), D outside N(a)
supplies the two region laws. Their coefficient counts retain every
natural order and no averaged feasibility premise. -/
theorem covered_region_coefficients_of_zero_body
    (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hRpos : 0 < μ (S.D ∩ S.rootNeighborhood a))
    (hEpos : 0 < μ (S.D \ S.rootNeighborhood a)) :
    let x := FiniteArity.rootedRegionCoefficients μ (PhysicalRepresentative.charge W m)
      ![{x | S.ρ x = r.val}, S.D ∩ S.rootNeighborhood a, S.D \ S.rootNeighborhood a]
    (∀ i, 0 ≤ x i) ∧ ∀ k l : ℕ,
      x 0 * k + x 1 * l - x 2 * k * ((k : ℝ) - 1) / 2 -
        x 3 * l * ((l : ℝ) - 1) / 2 - x 4 * k * l ≤ 1 := by
  exact S.conditional_rooted_coefficients_of_zero_body r hW hd hgap hzero
    (S.D ∩ S.rootNeighborhood a) (S.D \ S.rootNeighborhood a)
    (S.hD.inter (S.measurableSet_rootNeighborhood a))
    (S.hD.diff (S.measurableSet_rootNeighborhood a)) hRpos hEpos
    inter_subset_left sdiff_subset

/-- The three actual conditional diffuse penalties retain the original
gamma bound after averaging. No contact or averaged stationarity is assumed. -/
theorem conditional_rooted_penalty_mass_bounds
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (R E : Set Ω) (hR : MeasurableSet R) (hE : MeasurableSet E)
    (hRpos : 0 < μ R) (hEpos : 0 < μ E) (hRD : R ⊆ S.D) (hED : E ⊆ S.D) :
    let x := FiniteArity.rootedRegionCoefficients μ (PhysicalRepresentative.charge W m)
      ![{x | S.ρ x = r.val}, R, E]
    ∀ i : Fin 5, 2 ≤ i.val →
      2 * (c - m * d) + m ≤ μ.real {x | S.ρ x = r.val} * x i := by
  dsimp only
  let b := μ.real {x | S.ρ x = r.val}
  let γ := 2 * (c - m * d) + m
  let Y := PhysicalRepresentative.charge W m
  have hfloor : ∀ᵐ p ∂μ.prod μ, p.1 ∈ S.D → p.2 ∈ S.D → γ ≤ -b * Y p.1 p.2 := by
    filter_upwards [S.ae_body_penalty_mass_lower_of_zero_body r hW hd hgap hzero,
      S.hDcomplete, PhysicalRepresentative.charge_ae_eq W m
        (hW.strict_gap_structure hd hgap).strict_support] with p hf hc he hx hy
    have h := hf (S.row_ne_atom_of_mem_diffuse p.1 hx r)
      (S.row_ne_atom_of_mem_diffuse p.2 hy r) (hc hx hy)
    change γ ≤ -b * PhysicalRepresentative.charge W m p.1 p.2
    rw [he]
    exact h
  have havg (C D : Set Ω) (hC : MeasurableSet C) (hD : MeasurableSet D)
      (hCpos : 0 < μ C) (hDpos : 0 < μ D) (hCD : C ⊆ S.D) (hDD : D ⊆ S.D) :
      γ ≤ b * (-(∫ p, Y p.1 p.2 ∂(cond μ C).prod (cond μ D))) := by
    let ν := (cond μ C).prod (cond μ D)
    let : IsProbabilityMeasure (cond μ C) := cond_isProbabilityMeasure hCpos.ne'
    let : IsProbabilityMeasure (cond μ D) := cond_isProbabilityMeasure hDpos.ne'
    let : IsProbabilityMeasure ν := inferInstance
    have hac : ν ≪ μ.prod μ := cond_absolutelyContinuous.prod cond_absolutelyContinuous
    have hYint : Integrable (fun p : Ω × Ω => Y p.1 p.2) ν := Integrable.of_bound
      (PhysicalRepresentative.measurable_charge W m).aestronglyMeasurable 3
      (Eventually.of_forall (fun p => PhysicalRepresentative.charge_bound W m p.1 p.2))
    have hpoint : ∀ᵐ p ∂ν, γ ≤ -b * Y p.1 p.2 := by
        filter_upwards [hac.ae_le hfloor,
          Measure.quasiMeasurePreserving_fst.ae (ae_cond_mem hC),
          Measure.quasiMeasurePreserving_snd.ae (ae_cond_mem hD)] with p hp hx hy
        exact hp (hCD hx) (hDD hy)
    have hi := integral_mono_ae (integrable_const (μ := ν) γ) (hYint.const_mul (-b)) hpoint
    rw [integral_const, integral_const_mul] at hi
    simpa [ν, neg_mul, mul_neg] using hi
  intro i hi
  fin_cases i
  · norm_num at hi
  · norm_num at hi
  · exact havg R R hR hR hRpos hRpos hRD hRD
  · exact havg E E hE hE hEpos hEpos hED hED
  · exact havg R E hR hE hRpos hEpos hRD hED

/-- An explicit contact ratio for this original optimum makes all three
literal averaged penalties strictly greater than half of delta. -/
theorem conditional_rooted_penalties_gt_half_delta
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (R E : Set Ω) (hR : MeasurableSet R) (hE : MeasurableSet E)
    (hRpos : 0 < μ R) (hEpos : 0 < μ E) (hRD : R ⊆ S.D) (hED : E ⊆ S.D)
    (hratio : μ.real {x | S.ρ x = r.val} * (1 + m) < 2 * (2 * (c - m * d) + m)) :
    let x := FiniteArity.rootedRegionCoefficients μ (PhysicalRepresentative.charge W m)
      ![{x | S.ρ x = r.val}, R, E]
    ∀ i : Fin 5, 2 ≤ i.val → (1 + m) / 2 < x i := by
  dsimp only
  have hb : 0 < μ.real {x | S.ρ x = r.val} := ENNReal.toReal_pos
    (S.hfibers r.val r.property).2.1.ne' (measure_ne_top _ _)
  have hp := S.conditional_rooted_penalty_mass_bounds r hW hd hgap hzero
    R E hR hE hRpos hEpos hRD hED
  intro i hi
  have he := hp i hi
  nlinarith

end Erdos1017.CappedModel.SelectedHighLowStructure
