module

public import Erdos1017.Exclusions.Common.Covered.CoveredAtomCompletion
public import Erdos1017.Exclusions.Common.ZeroBody.SelectedZeroBodyCancellation
public import Erdos1017.Exclusions.Common.CliqueStarVariation
public import Erdos1017.SelectedModel.FullDiffuseCompletion

/-!
# Root charge floor on atoms in the zero-body branch

In the zero-body branch a positive independent atom cannot have all root charges
at most `-m`, every other independent whole atom has root charge strictly above
`-m`, and a saturated partner of the universal root misses every other exterior
independent whole atom.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

private theorem ae_atom_physical_independent (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → S.ρ p.2 = r.val →
      PhysicalRepresentative.adjacency W m p.1 p.2 = false := by
  have hi := (S.hfibers r.val r.property).2.2.1
  rw [Measure.prod_restrict] at hi
  have hi' := (ae_restrict_iff' ((S.hfibers r.val r.property).1.prod
    (S.hfibers r.val r.property).1)).mp hi
  filter_upwards [hi', PhysicalRepresentative.adjacency_moment_ae_eq W m
    (hW.strict_gap_structure hd hgap).strict_support] with p hp he hx hy
  have hz := hp ⟨hx, hy⟩
  change W.moment CappedColor.adjacency p = 0 at hz
  rw [hz] at he
  cases hA : PhysicalRepresentative.adjacency W m p.1 p.2
  · rfl
  · simp only [hA, ite_true] at he
    norm_num at he

/-- A positive independent atom cannot have all its root charges at most
`-m` when that independent root covers the original positive charge.
Actual completed feasibility is derived by deletion, and the old shifted
kernel pays for the exact-density return. -/
theorem not_ae_rootChargeRow_le_of_zero_body
    (S : SelectedHighLowStructure W m) (r u : S.I) (hru : r ≠ u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) :
    ¬(∀ᵐ x ∂μ.restrict {x | S.ρ x = u.val}, S.rootChargeRow r x ≤ -m) := by
  classical
  intro hle
  have hs := hW.strict_gap_structure hd hgap
  let R := {x | S.ρ x = r.val}
  let D := {x | S.ρ x = u.val}
  have hD : MeasurableSet D := (S.hfibers u.val u.property).1
  have hdisj : Disjoint R D := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hru (Subtype.ext (hx.symm.trans hy))
  have hbody : ∀ᵐ p ∂μ.prod μ, p.1 ∉ R → p.2 ∉ R →
      PhysicalRepresentative.charge W m p.1 p.2 ≤ 0 := by
    filter_upwards [S.zero_body_ae_charge_nonpositive r hzero,
      PhysicalRepresentative.charge_ae_eq W m hs.strict_support] with p hb he hx hy
    rw [he]
    exact hb hx hy
  have hle' : ∀ᵐ x ∂μ, x ∈ D → S.rootChargeRow r x ≤ -m :=
    (ae_restrict_iff' hD).mp hle
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    (S.ae_root_charge r hW hd hgap)
  have hstar : ∀ᵐ p ∂μ.prod μ, p.1 ∈ D → p.2 ∈ R →
      PhysicalRepresentative.charge W m p.1 p.2 ≤ -m := by
    filter_upwards [hswap, Measure.quasiMeasurePreserving_fst.ae hle'] with p hp hl hx hy
    have he : PhysicalRepresentative.charge W m p.2 p.1 = S.rootChargeRow r p.1 := hp hy
    rw [PhysicalRepresentative.charge_symm, he]
    exact hl hx
  have hcap := FiniteArity.feasibleOrder_complete_of_single_root μ
    (PhysicalRepresentative.adjacency W m) (PhysicalRepresentative.charge W m)
    (PhysicalRepresentative.adjacency_symm W m) (PhysicalRepresentative.charge_symm W m)
    R D hdisj (-m) (neg_nonneg.mpr hs.multiplier_neg.le)
    (S.ae_atom_physical_independent r hW hd hgap)
    (S.ae_atom_physical_independent u hW hd hgap) hbody hstar
    (PhysicalRepresentative.full_feasible W hW.full m hs.strict_support hW.deterministic)
  obtain ⟨v, hL, hQ⟩ := hW.exists_transverse_positive_direction hd hgap
  have hopt : objective W = FractionalGraph.densityLimit (density W) := by
    rw [hW.objective_eq, hW.density_eq]
    exact hW.optimal
  have hmass := ZeroCompletion.missingMass_eq_zero_of_full_optimum W hopt m
    (2 * (c - m * d)) hW.multiplier_mem hs.strict_support hW.stationary
    v hL hQ D hD (fun n _ => hcap n)
  have hcomplete := ZeroCompletion.ae_complete_of_missingMass_eq_zero W m D hD
    hs.strict_support hmass
  have hind := (S.hfibers u.val u.property).2.2.1
  rw [Measure.prod_restrict] at hind
  have hind' := (ae_restrict_iff' (hD.prod hD)).mp hind
  have hfalse : ∀ᵐ p ∂μ.prod μ, p.1 ∈ D → p.2 ∈ D → False := by
    filter_upwards [hcomplete, hind'] with p hc hi hx hy
    have he := hc hx hy
    have hz := hi ⟨hx, hy⟩
    change W.moment CappedColor.adjacency p = 0 at hz
    linarith
  obtain ⟨x, hx, hrow⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers u.val u.property).2.1.ne' (ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hfalse))
  obtain ⟨y, hy, hxy⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers u.val u.property).2.1.ne' (ae_restrict_of_ae hrow)
  exact hxy hx hy

/-- Every other original independent whole atom has root charge strictly
above `-m` in the zero-body branch. Homogeneity is derived from the two
actual whole-row fibers. No repeat test or completed-model premise is
supplied, and neither universality nor compactness is required. -/
theorem ae_rootChargeRow_gt_of_zero_body
    (S : SelectedHighLowStructure W m) (r u : S.I) (hru : r ≠ u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) :
    ∀ᵐ x ∂μ.restrict {x | S.ρ x = u.val}, -m < S.rootChargeRow r x := by
  obtain ⟨q, _, _, _, hc⟩ := KernelOperator.exists_whole_row_cross_block
    (shiftedKernel W m) (adjacencyKernel W) (chargeKernel W) 4 m S.ρ r.val u.val
    (S.hfibers r.val r.property).2.1 (S.hfibers u.val u.property).2.1
    (S.hfibers r.val r.property).2.2.2 (S.hfibers u.val u.property).2.2.2
    (shiftedKernel_measurable W m)
    (W.stronglyMeasurable_moment
      CappedColor.continuous_adjacency.measurable.stronglyMeasurable).aestronglyMeasurable
    (W.stronglyMeasurable_moment
      CappedColor.continuous_charge.measurable.stronglyMeasurable).aestronglyMeasurable
    ((shiftedMoment_symm W m).mono (fun _ hx => hx.symm)) hW.moment_mem
  let b := q + m * (if 0 < q then 1 else 0)
  have hb : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → S.ρ p.2 = u.val →
      chargeKernel W p.1 p.2 = b := by
    rw [Measure.prod_restrict] at hc
    have h := (ae_restrict_iff' ((S.hfibers r.val r.property).1.prod
      (S.hfibers u.val u.property).1)).mp hc
    exact h.mono (fun _ hp hr hu => (hp ⟨hr, hu⟩).2.2)
  have he := S.ae_rootChargeRow_on_constant_block r u hW hd hgap b hb
  have hblt : -m < b := by
    by_contra hnot
    apply S.not_ae_rootChargeRow_le_of_zero_body r u hru hW hd hgap hzero
    exact he.mono (fun _ hx => hx ▸ le_of_not_gt hnot)
  exact he.mono (fun _ hx => hx ▸ hblt)

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- A saturated partner of the universal root misses every other exterior
independent whole atom. Actual tight-parent cancellation and the derived
strict star floor contradict the original strict shifted support on any
such edge. -/
theorem ae_saturated_head_atom_adjacency_zero_of_zero_body
    (S : SelectedHighLowStructure W m) (r a u : S.I) (hru : r ≠ u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) :
    ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = a.val → S.ρ p.2 = u.val →
      adjacencyKernel W p.1 p.2 = 0 := by
  have hs := hW.strict_gap_structure hd hgap
  have hstar := S.ae_rootChargeRow_gt_of_zero_body r u hru hW hd hgap hzero
  have hstar' := (ae_restrict_iff' (S.hfibers u.val u.property).1).mp hstar
  filter_upwards [S.ae_saturated_head_charge_cancel_of_zero_body r a hW hd hgap hN hpair hzero,
    Measure.quasiMeasurePreserving_snd.ae hstar', hs.strict_support] with p hc ht hg ha hu
  have hur : S.ρ p.2 ≠ r.val := fun he => hru (Subtype.ext (he.symm.trans hu))
  change W.moment CappedColor.adjacency p = 0
  by_cases hpos : 0 < shiftedMoment W m p
  · have hG : adjacencyKernel W p.1 p.2 = 1 := by
      change W.moment CappedColor.adjacency p = 1
      simpa [hpos] using hg
    have he := hc ha hur hG
    have hgt := ht hu
    rw [shiftedMoment_eq] at hpos
    change W.moment CappedColor.adjacency p = 1 at hG
    change W.moment CappedColor.charge p + S.rootChargeRow r p.2 = 0 at he
    rw [hG] at hpos
    linarith
  · simpa [hpos] using hg

end Erdos1017.CappedModel.SelectedHighLowStructure
