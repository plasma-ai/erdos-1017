module

public import Erdos1017.Exclusions.Common.Physical.PhysicalDiffuseTriangleStar
public import Erdos1017.Exclusions.Common.SelectedRootRows

/-!
# Diffuse star bound in the selected model

Every diffuse coordinate of a tight physical triangle has star charge at most
minus the multiplier, even when the parent law is singular.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- Every diffuse coordinate of a tight original physical triangle has
star charge at most minus the original multiplier. The parent law may be
singular; only its distinct pair marginals are required to be AC. -/
theorem ae_permuted_diffuse_triangle_star_le
    (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (ρ : Measure (Fin 3 → Ω))
    (hpairs : ∀ i j : Fin 3, i ≠ j → ρ.map (fun v => (v i, v j)) ≪ μ.prod μ)
    (hclique : ∀ᵐ v ∂ρ, PhysicalCliqueRepresentative.Clique
      (Function.uncurry (PhysicalRepresentative.adjacency W m)) v)
    (htight : ∀ᵐ v ∂ρ, PhysicalPrimal.charge
      (Function.uncurry (PhysicalRepresentative.charge W m)) v = 1) :
    ∀ᵐ v ∂ρ, ∀ e : Equiv.Perm (Fin 3), v (e 0) ∈ S.D →
      PhysicalRepresentative.charge W m (v (e 0)) (v (e 1)) +
        PhysicalRepresentative.charge W m (v (e 0)) (v (e 2)) ≤ -m := by
  let G := Function.uncurry (PhysicalRepresentative.adjacency W m)
  let Y := Function.uncurry (PhysicalRepresentative.charge W m)
  have hs := hW.strict_gap_structure hd hgap
  have hfloor : ∀ᵐ p ∂μ.prod μ, p.1 ∈ S.D → p.2 ∈ S.D →
      G p = true ∧ -(-m) ≤ Y p := by
    filter_upwards [S.hDcomplete, hW.moment_mem,
      PhysicalRepresentative.adjacency_moment_ae_eq W m hs.strict_support,
      PhysicalRepresentative.charge_ae_eq W m hs.strict_support]
      with p hc hm ha hy hx hz
    have hA := hc hx hz
    have hG : G p = true := by
      rw [ha] at hA
      cases hg : PhysicalRepresentative.adjacency W m p.1 p.2 with
      | false => simp [hg] at hA
      | true => exact hg
    refine ⟨hG, ?_⟩
    change -(-m) ≤ PhysicalRepresentative.charge W m p.1 p.2
    simp only [neg_neg]
    rw [hy]
    rw [shiftedMoment_eq] at hm
    change m ≤ W.moment CappedColor.charge p
    rw [hc hx hz] at hm
    nlinarith [hm.1]
  have htest : ∀ᵐ v ∂Measure.pi (fun _ : Fin 4 => μ),
      PhysicalCliqueRepresentative.Clique G v → PhysicalPrimal.charge Y v ≤ 1 := by
    filter_upwards [PhysicalRepresentative.full_feasible W hW.full m hs.strict_support
      hW.deterministic 4] with v hv hc
    change PhysicalPrimal.charge (Function.uncurry (PhysicalRepresentative.charge W m)) v ≤ 1
    rw [MultipartiteHeadPrice.physicalCharge_eq_tupleCharge]
    exact hv hc
  exact PhysicalDiffuseTriangleStar.ae_permuted_triangle_star_le G
    (PhysicalRepresentative.measurable_adjacency W m) Y
    (PhysicalRepresentative.measurable_charge W m)
    (PhysicalRepresentative.charge_symm W m) 3 (by norm_num)
    (fun p => PhysicalRepresentative.charge_bound W m p.1 p.2)
    S.D S.hD (-m) hfloor htest ρ hpairs hclique htight

end Erdos1017.CappedModel.SelectedHighLowStructure
