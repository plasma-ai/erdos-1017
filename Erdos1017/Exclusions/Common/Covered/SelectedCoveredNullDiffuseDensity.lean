module

public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredNullDiffuse

/-!
# Exclusion of the null diffuse branch by density

With three atom labels and null `D` the original graph is bipartite with the
root fiber on one side, its density is determined exactly by the root mass, and
so the null-`D` branch is impossible at the original interior density
(`not_covered_null_diffuse`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  {W : Model Ω μ} {m : ℝ}

/-- Three original atom labels and null D give the actual original
bipartite graph, with root fiber on one side. This is a genuine
intermediate with its atom-exhaustion hypothesis displayed. -/
theorem ae_covered_null_diffuse_bipartite (S : SelectedHighLowStructure W m) (r a z : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) (hDnull : μ S.D = 0)
    (hrz : r ≠ z) (hatoms : ∀ u : S.I, u = r ∨ u = a ∨ u = z) :
    ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if (S.ρ p.1 = r.val ∧ S.ρ p.2 ≠ r.val) ∨
        (S.ρ p.1 ≠ r.val ∧ S.ρ p.2 = r.val) then 1 else 0 := by
  have hlabels : ∀ᵐ x ∂μ, ∃ u : S.I, S.ρ x = u.val := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hDnull] with x hx
    cases hq : S.coveredCountableBoundaryLabel x with
    | inl u => exact ⟨u, (S.coveredCountableBoundaryLabel_eq_inl_iff u x).mp hq⟩
    | inr flag =>
      cases flag
      exact False.elim (hx ((S.coveredCountableBoundaryLabel_eq_inr_iff x).mp hq))
  have hgraph (u v : S.I) :
      (if S.coveredGraph r a (Sum.inl u) (Sum.inl v) = true then (1 : ℝ) else 0) =
        if (u = r ∧ v ≠ r) ∨ (u ≠ r ∧ v = r) then 1 else 0 := by
    rcases hatoms u with rfl | rfl | rfl <;> rcases hatoms v with rfl | rfl | rfl <;>
      simp [coveredGraph, hpair.1, Ne.symm hpair.1, hrz, Ne.symm hrz]
  filter_upwards [S.ae_covered_atom_blocks r a hW hd hgap hpair hzero,
    Measure.quasiMeasurePreserving_fst.ae hlabels,
    Measure.quasiMeasurePreserving_snd.ae hlabels] with p hp hleft hright
  obtain ⟨u, hu⟩ := hleft
  obtain ⟨v, hv⟩ := hright
  change adjacencyKernel W p.1 p.2 = _
  rw [hp u v hu hv]
  have hux : u = r ↔ S.ρ p.1 = r.val := by rw [hu]; exact Subtype.ext_iff
  have hvx : v = r ↔ S.ρ p.2 = r.val := by rw [hv]; exact Subtype.ext_iff
  simpa only [ne_eq, hux, hvx] using hgraph u v

/-- The literal original root mass gives the exact bipartite density.
No objective or old-density assignment to a modified model is involved. -/
theorem covered_null_diffuse_density_eq (S : SelectedHighLowStructure W m) (r a z : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) (hDnull : μ S.D = 0)
    (hrz : r ≠ z) (hatoms : ∀ u : S.I, u = r ∨ u = a ∨ u = z) :
    d = μ.real {x | S.ρ x = r.val} * (1 - μ.real {x | S.ρ x = r.val}) := by
  let B := {x | S.ρ x = r.val}
  have hB : MeasurableSet B := (S.hfibers r.val r.property).1
  have hleft : Integrable ((B ×ˢ Bᶜ).indicator (fun _ : Ω × Ω => (1 : ℝ))) (μ.prod μ) :=
    (integrable_const 1).indicator (hB.prod hB.compl)
  have hright : Integrable ((Bᶜ ×ˢ B).indicator (fun _ : Ω × Ω => (1 : ℝ))) (μ.prod μ) :=
    (integrable_const 1).indicator (hB.compl.prod hB)
  have heq : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      (B ×ˢ Bᶜ).indicator (fun _ => (1 : ℝ)) p +
        (Bᶜ ×ˢ B).indicator (fun _ => (1 : ℝ)) p := by
    filter_upwards [S.ae_covered_null_diffuse_bipartite r a z hW hd hgap hpair
      hzero hDnull hrz hatoms] with p hp
    rw [hp]
    by_cases hx : S.ρ p.1 = r.val <;> by_cases hy : S.ρ p.2 = r.val <;>
      simp [B, hx, hy]
  rw [← hW.density_eq]
  unfold density
  rw [integral_congr_ae heq, integral_add hleft hright,
    integral_indicator (hB.prod hB.compl), integral_indicator (hB.compl.prod hB)]
  simp only [setIntegral_const, smul_eq_mul, mul_one, measureReal_prod_prod]
  rw [measureReal_compl hB, probReal_univ]
  change (μ.real B * (1 - μ.real B) + (1 - μ.real B) * μ.real B) / 2 = _
  ring

/-- The actual covered null-D branch is impossible at the original
interior density. Atom exhaustion and exact density are derived inside. -/
theorem not_covered_null_diffuse (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a) (hell : 1 / 2 < -m)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) (hDnull : μ S.D = 0)
    (hratio : μ.real {x | S.ρ x = r.val} * (1 + m) < 2 * (2 * (c - m * d) + m)) : False := by
  obtain ⟨z, hrz, hatoms⟩ := S.exists_covered_null_diffuse_three_label_cover r a hW hd hgap
    hpair hell hzero hDnull hratio
  have heq := S.covered_null_diffuse_density_eq r a z hW hd hgap hpair hzero hDnull hrz hatoms
  nlinarith [sq_nonneg (μ.real {x | S.ρ x = r.val} - 1 / 2), hd.1]

end Erdos1017.CappedModel.SelectedHighLowStructure
