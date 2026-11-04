module

public import Erdos1017.Exclusions.Common.CliqueStarVariation
public import Erdos1017.SelectedModel.SelectedHeadPeak
public import Erdos1017.Exclusions.Common.Physical.IndependentClassMissingMass

/-!
# Degree and mass bounds for an unsaturated universal root

A universal root's neighborhood is its exterior on a common event, the
unsaturated root repricer forces exterior degree at least twice the root mass
and missing capacity `1 - 2A` almost everywhere, and positive density forces the
root mass at most one half.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- A universal original root's literal neighborhood is its exterior on
one common vertex event, obtained from positive root sections. -/
theorem ae_universal_rootNeighborhood_iff (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    ∀ᵐ x ∂μ, x ∈ S.rootNeighborhood r ↔ S.ρ x ≠ r.val := by
  have hpair : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val →
      (p.2 ∈ S.rootNeighborhood r ↔ S.ρ p.2 ≠ r.val) := by
    filter_upwards [S.ae_original_root_adjacency r hW hd hgap,
      S.neutral_atom_adjacency r hW hd hgap hN] with p hn hg hr
    have he := (hn hr).symm.trans (hg hr)
    by_cases hne : S.ρ p.2 = r.val <;>
      by_cases hmem : p.2 ∈ S.rootNeighborhood r <;> simp_all
  obtain ⟨x, _, hx, hm⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers r.val r.property).2.1.ne'
    ((ae_restrict_of_ae (s := {x | S.ρ x = r.val})
      (Measure.ae_ae_of_ae_prod hpair)).and
        (ae_restrict_mem (S.hfibers r.val r.property).1))
  exact hx.mono (fun _ hy => hy hm)

/-- Strict original universal-star charge gives strict averaged root
charge on almost every exterior point, using a positive good root section. -/
theorem ae_unsaturated_universal_rootChargeRow (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hstar : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → S.ρ p.2 ≠ r.val →
      chargeKernel W p.1 p.2 < 1) :
    ∀ᵐ x ∂μ, S.ρ x ≠ r.val → S.rootChargeRow r x < 1 := by
  have hpair : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → S.ρ p.2 ≠ r.val →
      S.rootChargeRow r p.2 < 1 := by
    filter_upwards [S.ae_root_charge r hW hd hgap,
      PhysicalRepresentative.charge_ae_eq W m (hW.strict_gap_structure hd hgap).strict_support,
      hstar] with p hr hY hs hp he
    rw [← hr hp, hY]
    exact hs hp he
  obtain ⟨x, _, hx, hm⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers r.val r.property).2.1.ne'
    ((ae_restrict_of_ae (s := {x | S.ρ x = r.val})
      (Measure.ae_ae_of_ae_prod hpair)).and
        (ae_restrict_mem (S.hfibers r.val r.property).1))
  exact hx.mono (fun _ hy => hy hm)

/-- The actual universal root repricer forces exterior original degree at
least twice the root mass. One copy is the universal root block itself. -/
theorem ae_unsaturated_universal_degree_ge_twice_mass
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hstar : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → S.ρ p.2 ≠ r.val →
      chargeKernel W p.1 p.2 < 1) :
    ∀ᵐ x ∂μ, S.ρ x ≠ r.val →
      2 * μ.real {z | S.ρ z = r.val} ≤ ∫ z, adjacencyKernel W x z ∂μ := by
  let I := {x | S.ρ x = r.val}
  have hI : MeasurableSet I := (S.hfibers r.val r.property).1
  have hn := S.ae_universal_rootNeighborhood_iff r hW hd hgap hN
  have hsets : S.rootNeighborhood r =ᵐ[μ] Iᶜ := hn.mono (fun _ hx => propext hx)
  have hrow := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    (S.neutral_atom_adjacency r hW hd hgap hN)
  have hsym := adjacencyKernel_symm W
  filter_upwards [S.ae_original_root_degree_ge_mass r hW hd hgap, hn,
    S.ae_unsaturated_universal_rootChargeRow r hW hd hgap hstar,
    Measure.ae_ae_of_ae_prod (hrow.and hsym)] with x hl hn hs hr hx
  have hbound := hl (hn.mpr hx) (hs hx)
  rw [Measure.restrict_congr_set hsets] at hbound
  have hroot : (∫ z in I, adjacencyKernel W x z ∂μ) = μ.real {z | S.ρ z = r.val} := by
    have heq : ∀ᵐ z ∂μ.restrict I, adjacencyKernel W x z = 1 := by
      filter_upwards [ae_restrict_of_ae hr, ae_restrict_mem hI] with z hz hm
      have he := hz.1 hm
      change adjacencyKernel W z x = (if S.ρ x = r.val then 0 else 1) at he
      exact hz.2.trans (by simpa only [hx, ite_false] using he)
    rw [integral_congr_ae heq, setIntegral_const, smul_eq_mul, mul_one]
  have hi : Integrable (adjacencyKernel W x) μ := Integrable.of_bound
    ((W.stronglyMeasurable_moment
      CappedColor.continuous_adjacency.measurable.stronglyMeasurable).comp_measurable
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
    (Eventually.of_forall (fun z => by
      change ‖W.moment CappedColor.adjacency (x, z)‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (adjacency_moment_mem W (x, z)).1]
      exact (adjacency_moment_mem W (x, z)).2))
  have he := integral_add_compl hI hi
  rw [hroot] at he
  change μ.real {z | S.ρ z = r.val} ≤ ∫ z in Iᶜ, adjacencyKernel W x z ∂μ at hbound
  linarith

/-- Closed physical missing sections at almost every exterior vertex have
the actual capacity 1−2A supplied by the original unsaturated root edit. -/
theorem ae_unsaturated_universal_missing_capacity
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hstar : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → S.ρ p.2 ≠ r.val →
      chargeKernel W p.1 p.2 < 1) :
    ∀ᵐ x ∂μ, S.ρ x ≠ r.val →
      μ.real {z | PhysicalRepresentative.adjacency W m x z = false} ≤
        1 - 2 * μ.real {z | S.ρ z = r.val} := by
  filter_upwards [S.ae_unsaturated_universal_degree_ge_twice_mass r hW hd hgap hN hstar,
    Measure.ae_ae_of_ae_prod (PhysicalRepresentative.adjacency_moment_ae_eq W m
      (hW.strict_gap_structure hd hgap).strict_support)] with x hg hp hx
  let F := {z | PhysicalRepresentative.adjacency W m x z = false}
  have hF : MeasurableSet F :=
    (PhysicalRepresentative.measurable_adjacency W m).comp
      (measurable_const.prodMk measurable_id) (measurableSet_singleton false)
  have heq : F.indicator (fun _ : Ω => (1 : ℝ)) =ᵐ[μ]
      (fun z => 1 - adjacencyKernel W x z) := by
    filter_upwards [hp] with z hz
    change W.moment CappedColor.adjacency (x, z) = _ at hz
    change F.indicator (fun _ => (1 : ℝ)) z = 1 - W.moment CappedColor.adjacency (x, z)
    rw [hz]
    cases he : PhysicalRepresentative.adjacency W m x z <;> simp [F, he]
  have hi : Integrable (adjacencyKernel W x) μ := Integrable.of_bound
    ((W.stronglyMeasurable_moment
      CappedColor.continuous_adjacency.measurable.stronglyMeasurable).comp_measurable
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
    (Eventually.of_forall (fun z => by
      change ‖W.moment CappedColor.adjacency (x, z)‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (adjacency_moment_mem W (x, z)).1]
      exact (adjacency_moment_mem W (x, z)).2))
  have he := integral_congr_ae heq
  rw [integral_indicator hF, setIntegral_const, smul_eq_mul, mul_one,
    integral_sub (integrable_const 1) hi, integral_const, probReal_univ,
    smul_eq_mul, one_mul] at he
  change μ.real F ≤ _
  linarith [hg hx]

/-- Positive original density makes the universal exterior nonnull, so
its derived missing capacity forces the actual root mass at most one half. -/
theorem unsaturated_universal_mass_le_half
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hstar : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → S.ρ p.2 ≠ r.val →
      chargeKernel W p.1 p.2 < 1) :
    μ.real {z | S.ρ z = r.val} ≤ 1 / 2 := by
  let I := {z | S.ρ z = r.val}
  have hI : MeasurableSet I := (S.hfibers r.val r.property).1
  have hs : Summable (fun k => (S.originalAtomMass k) ^ 2) := by
    apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ S.originalAtomMass_summable.2
    intro k
    have h0 := S.originalAtomMass_summable.1 k
    have h1 : S.originalAtomMass k ≤ 1 := measureReal_le_one
    nlinarith
  have hsq := (hs.le_tsum r (fun _ _ => sq_nonneg _)).trans
    S.originalAtomMass_sq_sum_le_missing_density
  rw [hW.density_eq] at hsq
  have hA : μ.real I < 1 := by
    change (μ.real I) ^ 2 ≤ 1 - 2 * d at hsq
    nlinarith [hd.1]
  have hc : 0 < μ.real Iᶜ := by
    rw [measureReal_compl hI, probReal_univ]
    linarith
  have hcpos : 0 < μ Iᶜ := pos_iff_ne_zero.mpr (by
    intro hz
    rw [measureReal_def, hz, ENNReal.toReal_zero] at hc
    exact lt_irrefl _ hc)
  obtain ⟨x, _, hx, hm⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hcpos.ne'
    ((ae_restrict_of_ae (s := Iᶜ)
      (S.ae_unsaturated_universal_missing_capacity r hW hd hgap hN hstar)).and
        (ae_restrict_mem hI.compl))
  have hcap := hx hm
  have h0 : 0 ≤ μ.real {z | PhysicalRepresentative.adjacency W m x z = false} := measureReal_nonneg
  linarith

end Erdos1017.CappedModel.SelectedHighLowStructure
