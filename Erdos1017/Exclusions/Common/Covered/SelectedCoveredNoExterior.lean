module

public import Erdos1017.Exclusions.Common.Covered.CoveredCoefficientRepeatContexts
public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredFiveRegionEntry
public import Erdos1017.Exclusions.Common.Covered.CoveredCPhysicalExclusion

/-!
# No exterior atoms when both diffuse regions are positive

With positive `R` and `E`, the repeat witnesses and the own stationary
perturbation exclude every exterior atom, so the atoms are the root and the
saturated head (`covered_atoms_eq_root_or_saturated`); the finite-five model and
its scalar guards are constructed inside the proof.
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

/-- With positive R/E, the actual repeat witnesses and own stationary
perturbation exclude every exterior atom. The finite-five model and all
of its scalar guards are constructed from the same original optimum. -/
theorem covered_atoms_eq_root_or_saturated (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hR : 0 < μ (S.D ∩ S.rootNeighborhood a))
    (hE : 0 < μ (S.D \ S.rootNeighborhood a))
    (hell : 1 / 2 < -m)
    (hratio : μ.real {x | S.ρ x = r.val} * (1 + m) < 2 * (2 * (c - m * d) + m)) :
    ∀ u : S.I, u = r ∨ u = a := by
  intro u
  by_cases hur : u = r
  · exact Or.inl hur
  by_cases hua : u = a
  · exact Or.inr hua
  exfalso
  have hru : r ≠ u := Ne.symm hur
  have hau : a ≠ u := Ne.symm hua
  have hatoms := S.covered_atoms_eq_three r a u hW hd hgap hpair hzero hR hE hell hratio hru hau
  obtain ⟨V, hV, hmom, _, _, _, hx⟩ :=
    S.exists_covered_five_region_entry r a u hW hd hgap hpair hzero hR hE hur hua hatoms
  have hbare := S.coveredCoefficient_bare_repeat r a u hW hd hgap hpair hzero
    hR hE hell hratio hru hau
  have hm := S.ell_lt_one_of_exterior_atom r u hru hW hd hgap hzero
  have hBE : S.coveredGraph r a (Sum.inl r) (Sum.inr false) = true := by
    simp [coveredGraph, hpair.1]
  have hBu : S.coveredGraph r a (Sum.inl r) (Sum.inl u) = true := by
    simp [coveredGraph, hru, hpair.1]
  have huE : S.coveredGraph r a (Sum.inl u) (Sum.inr false) = true := by
    simp [coveredGraph, hua]
  have htri := S.coveredCoefficient_triangle r a hW hd hgap hpair hzero hR hE
    (Sum.inl r) (Sum.inl u) (Sum.inr false) hBu hBE huE
  have hfloor := S.coveredCoefficient_present_gt_m r a hW hd hgap hpair hzero hR hE
    (Sum.inl u) (Sum.inr false) huE
  have hv := S.coveredCoefficient_root_E_gt r a hW hd hgap hpair hzero hR hE
  have hpen (i j : Bool) : (1 + m) / 2 <
      -S.coveredCoefficient a (Sum.inr i) (Sum.inr j) :=
    S.coveredCoefficient_penalty_gt_half_delta r a hW hd hgap hpair hzero hR hE
      hratio (Sum.inr i) (Sum.inr j) (by simp) (by simp) rfl
  have huR : S.coveredGraph r a (Sum.inl u) (Sum.inr true) = true := by
    simp [coveredGraph]
  have hz := S.coveredCoefficient_penalty_gt_half_delta r a hW hd hgap hpair hzero hR hE
    hratio (Sum.inl u) (Sum.inr true) (by simp [hur]) (by simp) huR
  have hdc := S.coveredCoefficient_penalty_gt_half_delta r a hW hd hgap hpair hzero hR hE
    hratio (Sum.inl u) (Sum.inr false) (by simp [hur]) (by simp) huE
  apply CoveredC.not_fullStationaryClass_of_moments hV (S.coveredFiveLabel r a)
    (S.measurable_coveredFiveLabel r a)
    (S.coveredFiveLabel_fibers_positive r a u hpair.1 hur hua hatoms hR hE)
    (S.coveredEntry r a) hx (S.coveredCEntry r a u 0) (S.coveredCEntry r a u 1)
    (S.coveredCEntry r a u 2) _ _ _ _ _ _ _ hmom
  · change S.coveredCoefficient a (Sum.inl r) (Sum.inl u) < 1
    linarith
  · change 0 < -S.coveredCoefficient a (Sum.inl u) (Sum.inr true)
    linarith
  · change 0 < -S.coveredCoefficient a (Sum.inl u) (Sum.inr false)
    linarith
  · change 1 - S.coveredCoefficient a (Sum.inl r) (Sum.inl u) <
      -S.coveredCoefficient a (Sum.inr true) (Sum.inr true)
    linarith [hpen true true]
  · change 1 - S.coveredCoefficient a (Sum.inl r) (Sum.inl u) <
      -S.coveredCoefficient a (Sum.inr false) (Sum.inr false)
    linarith [hpen false false]
  · change 1 - S.coveredCoefficient a (Sum.inl r) (Sum.inl u) <
      -S.coveredCoefficient a (Sum.inr true) (Sum.inr false)
    linarith [hpen true false]
  · exact hv

end Erdos1017.CappedModel.SelectedHighLowStructure
