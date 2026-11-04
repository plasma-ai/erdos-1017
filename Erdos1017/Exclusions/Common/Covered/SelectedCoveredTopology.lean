module

public import Erdos1017.Exclusions.Common.SelectedMissingNeighborhood
public import Erdos1017.Exclusions.Common.ZeroBody.SelectedZeroBodyTopology

/-!
# Adjacency of the exterior atoms in the zero-body branch

In the covered zero-body branch, distinct exterior atoms form a complete
multipartite graph and every exterior atom sees the entire diffuse part, all on
one product-law event even when the atom family is infinite.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  {W : Model Ω μ} {m : ℝ}

private theorem ae_atom_outside_saturated_neighborhood
    (S : SelectedHighLowStructure W m) (r a u : S.I) (hru : r ≠ u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) :
    ∀ᵐ x ∂μ, S.ρ x = u.val → x ∉ S.rootNeighborhood a := by
  have hblock := S.ae_saturated_head_atom_adjacency_zero_of_zero_body
    r a u hru hW hd hgap hN hpair hzero
  have hn := S.ae_rootNeighborhood_on_constant_block a u hW hd hgap false
    (by simpa using hblock)
  simpa using hn

/-- Distinct exterior atoms in the covered zero-body branch form an
actual complete multipartite graph. The common original cut, rather than
an edited model's selected structure, supplies the missing-neighborhood
comparison. -/
theorem ae_exterior_atoms_adjacent_of_zero_body
    (S : SelectedHighLowStructure W m) (r a u v : S.I)
    (hru : r ≠ u) (hau : a ≠ u) (hrv : r ≠ v) (hav : a ≠ v) (huv : u ≠ v)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) :
    ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = u.val → S.ρ p.2 = v.val →
      adjacencyKernel W p.1 p.2 = 1 := by
  have hu := S.ae_atom_outside_saturated_neighborhood r a u hru hW hd hgap hN hpair hzero
  have hv := S.ae_atom_outside_saturated_neighborhood r a v hrv hW hd hgap hN hpair hzero
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hu,
    Measure.quasiMeasurePreserving_snd.ae hv,
    S.ae_missing_neighborhood_complete_mod_rows a hW hd hgap] with p hx hy hc hxU hyV
  apply hc
  · exact fun he => hau (Subtype.ext (he.symm.trans hxU))
  · exact fun he => hav (Subtype.ext (he.symm.trans hyV))
  · exact hx hxU
  · exact hy hyV
  · exact fun he => huv (Subtype.ext (hxU.symm.trans (he.trans hyV)))

/-- Every exterior independent atom sees the entire original diffuse
part. On the saturated head's neighborhood this is the actual neutral
exchange theorem; on its complement it follows from the original cut. -/
theorem ae_exterior_atom_sees_diffuse_of_zero_body
    (S : SelectedHighLowStructure W m) (r a u : S.I) (hru : r ≠ u) (hau : a ≠ u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) :
    ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = u.val → p.2 ∈ S.D →
      adjacencyKernel W p.1 p.2 = 1 := by
  have hu := S.ae_atom_outside_saturated_neighborhood r a u hru hW hd hgap hN hpair hzero
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hu,
    S.ae_missing_neighborhood_complete_mod_rows a hW hd hgap,
    S.ae_atom_sees_diffuse_saturated_neighbors_of_zero_body
      r a u hru hau hW hd hgap hN hpair hzero] with p hx hc he hxU hyD
  by_cases hyA : p.2 ∈ S.rootNeighborhood a
  · exact he hxU hyD hyA
  · apply hc
    · exact fun hf => hau (Subtype.ext (hf.symm.trans hxU))
    · exact S.row_ne_atom_of_mem_diffuse p.2 hyD a
    · exact hx hxU
    · exact hyA
    · exact fun hf => S.row_ne_atom_of_mem_diffuse p.2 hyD u (hf.symm.trans hxU)

/-- One original product-law event carries all exterior atom blocks and
all atom-to-diffuse blocks, even when the original atom family is infinite. -/
theorem ae_all_exterior_adjacency_of_zero_body
    (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) :
    ∀ᵐ p ∂μ.prod μ, ∀ u : S.I, r ≠ u → a ≠ u → S.ρ p.1 = u.val →
      (p.2 ∈ S.D → adjacencyKernel W p.1 p.2 = 1) ∧
      (∀ v : S.I, r ≠ v → a ≠ v → u ≠ v → S.ρ p.2 = v.val →
        adjacencyKernel W p.1 p.2 = 1) := by
  let : Countable S.I := S.hI.to_subtype
  apply ae_all_iff.mpr
  intro u
  by_cases hru : r = u
  · exact Filter.Eventually.of_forall (by simp [hru])
  by_cases hau : a = u
  · exact Filter.Eventually.of_forall (by simp [hau])
  have hblocks : ∀ᵐ p ∂μ.prod μ, ∀ v : S.I, r ≠ v → a ≠ v → u ≠ v →
      S.ρ p.1 = u.val → S.ρ p.2 = v.val → adjacencyKernel W p.1 p.2 = 1 := by
    apply ae_all_iff.mpr
    intro v
    by_cases hrv : r = v
    · exact Filter.Eventually.of_forall (by simp [hrv])
    by_cases hav : a = v
    · exact Filter.Eventually.of_forall (by simp [hav])
    by_cases huv : u = v
    · exact Filter.Eventually.of_forall (by simp [huv])
    exact (S.ae_exterior_atoms_adjacent_of_zero_body r a u v hru hau hrv hav huv
      hW hd hgap hN hpair hzero).mono (fun _ h _ _ _ => h)
  filter_upwards [hblocks,
    S.ae_exterior_atom_sees_diffuse_of_zero_body r a u hru hau hW hd hgap hN hpair hzero]
    with p hb hdif _ _ hu
  exact ⟨hdif hu, fun v hrv hav huv hv => hb v hrv hav huv hu hv⟩

end Erdos1017.CappedModel.SelectedHighLowStructure
