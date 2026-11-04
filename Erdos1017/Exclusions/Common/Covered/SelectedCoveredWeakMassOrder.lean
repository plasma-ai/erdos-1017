module

public import Erdos1017.Exclusions.Common.Saturation.SelectedSaturatedParentCounts
public import Erdos1017.Exclusions.Common.Physical.PhysicalResidualCountTightness

/-!
# Weak mass order of the covered regions

From the saturated-parent counts, the `AR` demand cannot exceed the `AB` demand
(`covered_R_mass_le_root`), without any coefficient-sign or strict mass-order
premise.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  {W : Model Ω μ} {m : ℝ}

/-- Original saturated-parent counts give the weak region-mass order:
AR demand cannot exceed AB demand. No active coefficient signs or
strict mass-order premise is used. -/
theorem covered_R_mass_le_root (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) :
    μ.real (S.D ∩ S.rootNeighborhood a) ≤ μ.real {x | S.ρ x = r.val} := by
  obtain ⟨P, hroot, _⟩ := S.exists_rooted_primal_of_zero_body r hW hd hgap hzero
  let : ∀ n, IsFiniteMeasure (P.laws n) := P.finite
  let I := {x | S.ρ x = r.val}
  let A := {x | S.ρ x = a.val}
  let R := S.D ∩ S.rootNeighborhood a
  let G := {p : Ω × Ω | PhysicalRepresentative.adjacency W m p.1 p.2 = true}
  let demand := PhysicalPrimal.graphDemand μ G
  let : IsFiniteMeasure demand := by
    dsimp only [demand, PhysicalPrimal.graphDemand]
    infer_instance
  have hI : MeasurableSet I := (S.hfibers r.val r.property).1
  have hA : MeasurableSet A := (S.hfibers a.val a.property).1
  have hR : MeasurableSet R := S.hD.inter (S.measurableSet_rootNeighborhood a)
  have hIA : Disjoint I A := Set.disjoint_left.mpr (fun _ hx hy =>
    hpair.1 (Subtype.ext (hx.symm.trans hy)))
  have hAR : Disjoint A R := Set.disjoint_left.mpr (fun x hx hy =>
    S.row_ne_atom_of_mem_diffuse x hy.1 a hx)
  have hcap (n : ℕ) (hn : P.orderCap < n) : P.laws n = 0 := P.capped n (Or.inr hn)
  let θ := PhysicalPrimal.countMeasure P.orderCap P.laws A R
  have hle : ∀ᵐ z ∂θ, (z.1 : ℝ) * (z.2 : ℝ) ≤ (z.1 : ℝ) := by
    apply PhysicalPrimal.ae_countMeasure P.orderCap P.laws A R hA hR
    intro n
    filter_upwards [P.ae_saturated_parent_count_shape a hW hd hgap hpair hzero n]
      with v hv
    by_cases ha : ∃ i, v i ∈ A
    · have hk : (PhysicalPrimal.tupleCount R v : ℝ) ≤ 1 := by
        exact_mod_cast (hv ha).2.2
      have hAc : PhysicalPrimal.tupleCount A v = 1 := (hv ha).1
      rw [hAc, Nat.cast_one, one_mul]
      exact hk
    · have hn : ∀ i, v i ∉ A := by simpa only [not_exists] using ha
      simp [PhysicalPrimal.tupleCount, hn]
  have hi := PhysicalPrimal.integrable_countMeasure P.orderCap P.laws A R hA hR
  have hineq := integral_mono_ae (hi (fun z => (z.1 : ℝ) * (z.2 : ℝ)))
    (hi (fun z => (z.1 : ℝ))) hle
  rw [PhysicalPrimal.countMeasure_cross_moment P.orderCap P.laws A R hA hR hAR
    hcap demand P.feasible.2.2.2,
    PhysicalPrimal.countMeasure_first_moment P.orderCap P.laws I A R hI hA hR hIA
      hroot hcap demand P.feasible.2.2.2] at hineq
  have hIAvalue : demand.real (I ×ˢ A) = μ.real I * μ.real A :=
    PhysicalPrimal.graphDemand_real_rectangle μ G I A hI hA (by
      filter_upwards [S.ae_root_universal_of_zero_body r hW hd hgap hzero] with p hp hx hy
      exact (hp hx).mpr (fun he => hpair.1 (Subtype.ext (he.symm.trans hy))))
  have hARvalue : demand.real (A ×ˢ R) = μ.real A * μ.real R :=
    PhysicalPrimal.graphDemand_real_rectangle μ G A R hA hR (by
      filter_upwards [S.ae_root_adjacency a hW hd hgap] with p hp hx hy
      exact (hp hx).mpr hy.2)
  rw [hIAvalue, hARvalue] at hineq
  have ha : 0 < μ.real A := ENNReal.toReal_pos
    (S.hfibers a.val a.property).2.1.ne' (measure_ne_top _ _)
  dsimp only [I, R] at hineq ⊢
  nlinarith

end Erdos1017.CappedModel.SelectedHighLowStructure
