module

public import Erdos1017.Exclusions.Common.SelectedRootRepricing
public import Erdos1017.SelectedModel.Saturation.SelectedSaturatedPairBlocks
public import Erdos1017.SelectedModel.Saturation.SelectedSaturatedPairOrientation
public import Erdos1017.Exclusions.Common.SelectedAtomDiffuseCharge
public import Erdos1017.Exclusions.Common.Private.SelectedPrivateBodyInventory
public import Erdos1017.Exclusions.Common.CliqueStarVariation

/-!
# Root stars and neighbor degrees of a high whole atom

A positive original high whole atom has strict charge slack against almost every
vertex, in the one-hole case the root neighborhood is the complement of the two
independent whole fibers, and a private neighbor's missing section has capacity
at most `1 - 2A - b`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- A positive original HIGH whole atom has strict charge slack against
almost every original vertex. Saturated whole blocks and atom–diffuse
charge one are both excluded by the actual selected model. -/
theorem ae_rootChargeRow_lt_one_of_high_fiber
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.H) :
    ∀ᵐ y ∂μ, S.rootChargeRow r y < 1 := by
  let : Countable S.I := S.hI.to_subtype
  let Ir := {x | S.ρ x = r.val}
  have hIr := S.hfibers r.val r.property
  have hnot (u : S.I) (hru : r ≠ u) : ¬S.IsSaturatedAtomPair r u := by
    intro hpair
    have hz := hpair.high_head_null hW hd hgap hell
    have hnotH : ∀ᵐ x ∂μ.restrict Ir, x ∉ S.H := by
      filter_upwards [ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp hz),
        ae_restrict_mem hIr.1] with x hx hi hH
      exact hx ⟨hi, hH⟩
    obtain ⟨x, _, hh, hn⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      hIr.2.1.ne' (hhigh.and hnotH)
    exact hn hh
  have hatom : ∀ᵐ y ∂μ, ∀ u : S.I, S.ρ y = u.val → S.rootChargeRow r y < 1 := by
    apply ae_all_iff.mpr
    intro u
    by_cases hru : r = u
    · subst u
      filter_upwards [S.rootChargeRow_zero_off_neighborhood r hW hd hgap] with y hy hyr
      have hn : y ∉ S.rootNeighborhood r :=
        Set.disjoint_left.mp (S.rootNeighborhood_disjoint r) hyr
      rw [hy hn]
      norm_num
    · exact (ae_restrict_iff' (S.hfibers u.val u.property).1).mp
        (S.ae_rootChargeRow_lt_one_of_not_saturated r u hru hW hd hgap (hnot u hru))
  have hdiff : ∀ᵐ y ∂μ, y ∈ S.D → S.rootChargeRow r y < 1 := by
    have hp : ∀ᵐ p ∂μ.prod μ, p.1 ∈ Ir → p.2 ∈ S.D → S.rootChargeRow r p.2 < 1 := by
      filter_upwards [S.ae_root_charge r hW hd hgap,
        PhysicalRepresentative.charge_ae_eq W m
          (hW.strict_gap_structure hd hgap).strict_support,
        S.charge_lt_one_on_atom_diffuse hW hd hgap hell r] with p hr he hc hx hy
      rw [← hr hx, he]
      exact hc hx hy
    obtain ⟨x, hx, hrow⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      hIr.2.1.ne' ((ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hp)).and
        (ae_restrict_mem hIr.1))
    exact hrow.1.mono (fun _ hy hD => hy hrow.2 hD)
  filter_upwards [hatom, hdiff] with y ha hD
  by_cases hyD : y ∈ S.D
  · exact hD hyD
  · have hu : y ∈ ⋃ u ∈ S.I, {x | S.ρ x = u} := by
      simpa only [S.hDeq, mem_compl_iff, not_not] using hyD
    obtain ⟨u, hyu⟩ := mem_iUnion.mp hu
    obtain ⟨huI, hyu⟩ := mem_iUnion.mp hyu
    exact ha ⟨u, huI⟩ hyu

/-- Signed root repricing supplies the original neighborhood degree for
the same HIGH whole atom, with strict root-charge slack proved above. -/
theorem ae_original_root_degree_ge_mass_of_high_fiber
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.H) :
    ∀ᵐ x ∂μ, x ∈ S.rootNeighborhood r →
      μ.real {z | S.ρ z = r.val} ≤
        ∫ z in S.rootNeighborhood r, adjacencyKernel W x z ∂μ := by
  filter_upwards [S.ae_original_root_degree_ge_mass r hW hd hgap,
    S.ae_rootChargeRow_lt_one_of_high_fiber r hW hd hgap hell hhigh]
    with x hd hs hx
  exact hd hx hs

/-- In the genuine one-hole case the original root neighborhood is the
complement of the two original independent whole fibers, modulo the
original measure. -/
theorem ae_private_rootNeighborhood_iff
    (S : SelectedHighLowStructure W m) (r u : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hprivate : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val →
      adjacencyKernel W p.1 p.2 =
        if S.ρ p.2 = r.val ∨ S.ρ p.2 = u.val then 0 else 1) :
    ∀ᵐ x ∂μ, x ∈ S.rootNeighborhood r ↔
      S.ρ x ≠ r.val ∧ S.ρ x ≠ u.val := by
  let I := {x | S.ρ x = r.val}
  have hI := S.hfibers r.val r.property
  have hpair : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I →
      (p.2 ∈ S.rootNeighborhood r ↔
        S.ρ p.2 ≠ r.val ∧ S.ρ p.2 ≠ u.val) := by
    filter_upwards [hprivate, PhysicalRepresentative.adjacency_moment_ae_eq W m
      (hW.strict_gap_structure hd hgap).strict_support,
      S.ae_root_adjacency r hW hd hgap] with p hp he hr hi
    have hvalue := he.symm.trans (hp hi)
    change (if PhysicalRepresentative.adjacency W m p.1 p.2 = true then (1 : ℝ) else 0) =
      (if S.ρ p.2 = r.val ∨ S.ρ p.2 = u.val then 0 else 1) at hvalue
    have hb : PhysicalRepresentative.adjacency W m p.1 p.2 = true ↔
        S.ρ p.2 ≠ r.val ∧ S.ρ p.2 ≠ u.val := by
      cases hA : PhysicalRepresentative.adjacency W m p.1 p.2 <;>
        by_cases hr : S.ρ p.2 = r.val <;>
        by_cases hu : S.ρ p.2 = u.val <;> simp_all
    exact (hr hi).symm.trans hb
  obtain ⟨x, hx, hrow⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    hI.2.1.ne' ((ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hpair)).and
      (ae_restrict_mem hI.1))
  exact hrow.1.mono (fun _ hy => hy hrow.2)

/-- A vertex in an actual original root neighborhood sees almost every
point of that positive whole fiber under the original adjacency kernel. -/
theorem ae_root_cross_adjacency_one
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ p ∂μ.prod μ, p.1 ∈ S.rootNeighborhood r →
      S.ρ p.2 = r.val → adjacencyKernel W p.1 p.2 = 1 := by
  have hroot : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val →
      p.2 ∈ S.rootNeighborhood r → adjacencyKernel W p.1 p.2 = 1 := by
    filter_upwards [S.ae_root_adjacency r hW hd hgap,
      PhysicalRepresentative.adjacency_moment_ae_eq W m
        (hW.strict_gap_structure hd hgap).strict_support] with p hp he hr hn
    change W.moment CappedColor.adjacency p = 1
    rw [he, (hp hr).mpr hn]
    norm_num
  have hsw := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    hroot
  filter_upwards [hsw, adjacencyKernel_symm W] with p hp hs hn hr
  exact hs.trans (hp hr hn)

/-- A vertex in the original private neighbor region sees both whole
fibers and retains at least one additional root mass of adjacency in
the exterior. The exterior root-degree bound is derived above. -/
theorem ae_private_neighbor_degree_ge
    (S : SelectedHighLowStructure W m) (r u : S.I) (hru : r ≠ u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.H)
    (hprivate : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val →
      adjacencyKernel W p.1 p.2 =
        if S.ρ p.2 = r.val ∨ S.ρ p.2 = u.val then 0 else 1) :
    ∀ᵐ x ∂μ, x ∈ ({z | S.ρ z = r.val} ∪ {z | S.ρ z = u.val})ᶜ ∩
        S.rootNeighborhood u →
      2 * μ.real {z | S.ρ z = r.val} + μ.real {z | S.ρ z = u.val} ≤
        ∫ z, adjacencyKernel W x z ∂μ := by
  let I := {z | S.ρ z = r.val}
  let P := {z | S.ρ z = u.val}
  let E := I ∪ P
  have hI := (S.hfibers r.val r.property).1
  have hP := (S.hfibers u.val u.property).1
  have hE : MeasurableSet E := hI.union hP
  have hdis : Disjoint I P := Set.disjoint_left.mpr (fun _ hx hy =>
    hru (Subtype.ext (hx.symm.trans hy)))
  have hV : S.rootNeighborhood r =ᵐ[μ] Eᶜ :=
    (S.ae_private_rootNeighborhood_iff r u hW hd hgap hprivate).mono
      (fun _ hx => propext (by simpa only [E, I, P, mem_compl_iff, mem_union,
        mem_ofPred_eq, not_or] using hx))
  have hrowI := Measure.ae_ae_of_ae_prod (S.ae_root_cross_adjacency_one r hW hd hgap)
  have hrowP := Measure.ae_ae_of_ae_prod (S.ae_root_cross_adjacency_one u hW hd hgap)
  filter_upwards [S.ae_original_root_degree_ge_mass_of_high_fiber r hW hd hgap hell hhigh,
    hV, hrowI, hrowP] with x hroot hVx hIrow hProw hx
  have hxV : x ∈ S.rootNeighborhood r := hVx.mpr hx.1
  have hbound := hroot hxV
  rw [Measure.restrict_congr_set hV] at hbound
  have hIr : (∫ z in I, adjacencyKernel W x z ∂μ) = μ.real I := by
    have heq : ∀ᵐ z ∂μ.restrict I, adjacencyKernel W x z = 1 := by
      filter_upwards [ae_restrict_of_ae hIrow, ae_restrict_mem hI] with z hz hi
      exact hz hxV hi
    rw [integral_congr_ae heq, setIntegral_const, smul_eq_mul, mul_one]
  have hPr : (∫ z in P, adjacencyKernel W x z ∂μ) = μ.real P := by
    have heq : ∀ᵐ z ∂μ.restrict P, adjacencyKernel W x z = 1 := by
      filter_upwards [ae_restrict_of_ae hProw, ae_restrict_mem hP] with z hz hi
      exact hz hx.2 hi
    rw [integral_congr_ae heq, setIntegral_const, smul_eq_mul, mul_one]
  have hi : Integrable (adjacencyKernel W x) μ := Integrable.of_bound
    ((W.stronglyMeasurable_moment
      CappedColor.continuous_adjacency.measurable.stronglyMeasurable).comp_measurable
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
    (Eventually.of_forall (fun z => by
      change ‖W.moment CappedColor.adjacency (x, z)‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (adjacency_moment_mem W (x, z)).1]
      exact (adjacency_moment_mem W (x, z)).2))
  have hEr : (∫ z in E, adjacencyKernel W x z ∂μ) = μ.real I + μ.real P := by
    rw [show E = I ∪ P from rfl,
      setIntegral_union hdis hP hi.integrableOn hi.integrableOn, hIr, hPr]
  have htotal := integral_add_compl hE hi
  rw [hEr] at htotal
  change μ.real I ≤ ∫ z in Eᶜ, adjacencyKernel W x z ∂μ at hbound
  change 2 * μ.real I + μ.real P ≤ ∫ z, adjacencyKernel W x z ∂μ
  linarith

/-- The original physical missing section of a private neighbor has
capacity at most `1 - 2A - b`. The original degree bound and Boolean
representative identity are both established on the same old law. -/
theorem ae_private_neighbor_missing_capacity
    (S : SelectedHighLowStructure W m) (r u : S.I) (hru : r ≠ u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.H)
    (hprivate : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val →
      adjacencyKernel W p.1 p.2 =
        if S.ρ p.2 = r.val ∨ S.ρ p.2 = u.val then 0 else 1) :
    ∀ᵐ x ∂μ, x ∈ ({z | S.ρ z = r.val} ∪ {z | S.ρ z = u.val})ᶜ ∩
        S.rootNeighborhood u →
      μ.real {z | PhysicalRepresentative.adjacency W m x z = false} ≤
        1 - 2 * μ.real {z | S.ρ z = r.val} - μ.real {z | S.ρ z = u.val} := by
  filter_upwards [S.ae_private_neighbor_degree_ge r u hru hW hd hgap hell hhigh hprivate,
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

end Erdos1017.CappedModel.SelectedHighLowStructure
