module

public import Erdos1017.SelectedModel.Selection.FullStrictGapPhysicalPrimal
public import Erdos1017.Multipartite.MultipartiteLowDensity

/-!
# Saturated charge mass from the physical primal

The physical primal of a strict-gap full optimum forces a lower bound on the
original saturated charge mass (`saturated_charge_mass_lower_bound`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators ENNReal

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]
  [StandardBorelSpace Ω] [MeasurableEq Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NullSingletonClass μ] [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- The actual physical primal of the same strict-gap full optimum forces
original saturated charge mass. All laws and their tightness are constructed
internally; no joint absolute continuity of parent laws is assumed. -/
theorem FullStationaryClass.saturated_charge_mass_lower_bound
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hdhalf : d < 1 / 2) (hgap : benchmark d < c) :
    (3 * c - d) / 2 ≤ (μ.prod μ).real {p | W.moment CappedColor.charge p = 1} / 2 := by
  let A : Ω × Ω → ℝ := W.moment CappedColor.adjacency
  let Y : Ω × Ω → ℝ := W.moment CappedColor.charge
  let Λ := (μ.prod μ).withDensity (fun p => ENNReal.ofReal (A p))
  let T : Set (Ω × Ω) := {p | Y p = 1}
  have hA0 (p : Ω × Ω) : 0 ≤ A p := (adjacency_moment_mem W p).1
  have hA1 (p : Ω × Ω) : A p ≤ 1 := (adjacency_moment_mem W p).2
  have hY1 (p : Ω × Ω) : Y p ≤ 1 :=
    (charge_moment_le_adjacency W p).trans (hA1 p)
  have hsat (p : Ω × Ω) (hp : p ∈ T) : A p = 1 := by
    have hYA := charge_moment_le_adjacency W p
    change Y p = 1 at hp
    exact le_antisymm (hA1 p) (by change 1 ≤ A p; linarith)
  have hYm : Measurable Y :=
    (W.stronglyMeasurable_moment
      CappedColor.continuous_charge.measurable.stronglyMeasurable).measurable
  have hT : MeasurableSet T := measurableSet_eq_fun hYm measurable_const
  have hdom : Λ ≤ μ.prod μ := by
    calc
      Λ ≤ (μ.prod μ).withDensity (fun _ => (1 : ℝ≥0∞)) :=
        withDensity_mono (Eventually.of_forall (fun p => by
          simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (hA1 p)))
      _ = μ.prod μ := withDensity_one
  let : IsFiniteMeasure Λ := isFiniteMeasure_of_le (μ.prod μ) hdom
  have hmass : Λ.real univ = 2 * d := by
    have heq : Λ.real univ = ∫ p, A p ∂μ.prod μ := by
      rw [measureReal_def, show Λ = (μ.prod μ).withDensity (fun p => ENNReal.ofReal (A p)) from rfl,
        withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      exact (integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hA0)
        (adjacencyKernel_measurable W)).symm
    have hd := hW.density_eq
    change (∫ p, A p ∂μ.prod μ) / 2 = d at hd
    rw [heq]
    linarith
  have hsatmass : Λ T = (μ.prod μ) T := by
    rw [show Λ = (μ.prod μ).withDensity (fun p => ENNReal.ofReal (A p)) from rfl,
      withDensity_apply _ hT]
    have heq : (fun p => ENNReal.ofReal (A p)) =ᵐ[(μ.prod μ).restrict T] 1 := by
      filter_upwards [ae_restrict_mem hT] with p hp
      rw [hsat p hp]
      exact ENNReal.ofReal_one
    rw [lintegral_congr_ae heq]
    change (∫⁻ _p, (1 : ℝ≥0∞) ∂(μ.prod μ).restrict T) = (μ.prod μ) T
    simp
  obtain ⟨_, _, _, η, hfinite, _, _, hfeasible, hcost, _, htight⟩ :=
    hW.exists_physical_primal_of_strict_gap hdhalf hgap
  let : ∀ n, IsFiniteMeasure (η n) := hfinite
  have hbalance : PhysicalPrimal.occupation η = Λ := hfeasible.2.2.2
  have hcount := PhysicalPrimal.three_cost_le_pair_mass η Λ
    hfeasible.1 hfeasible.2.1 hbalance
  rw [hcost, hmass] at hcount
  let ρ := PhysicalPrimal.orderOccupation 2 (η 2)
  have hρdom : ρ ≤ Λ := by
    rw [← hbalance]
    exact Measure.le_sum (fun n => PhysicalPrimal.orderOccupation n (η n)) 2
  let : IsFiniteMeasure ρ := isFiniteMeasure_of_le Λ hρdom
  have hρmass : ρ.real univ = 2 * (η 2).real univ := by
    rw [show ρ = PhysicalPrimal.orderOccupation 2 (η 2) from rfl,
      PhysicalPrimal.orderOccupation_mass]
    norm_num [show Fintype.card (PhysicalPrimal.PairIndex 2) = 2 by decide]
  have hYi : Integrable Y (μ.prod μ) :=
    Integrable.of_bound (chargeKernel_measurable W) 3 (chargeKernel_bound W)
  have hYρ : Integrable Y ρ := hYi.mono_measure (hρdom.trans hdom)
  have hcharge := (PhysicalPrimal.integral_charge 2 (η 2) Y hYρ).2
  have ht : (∫ v, PhysicalPrimal.charge Y v ∂η 2) = (η 2).real univ := by
    have hYeq : Function.uncurry (chargeKernel W) = Y := by
      funext p
      rcases p with ⟨a, b⟩
      rfl
    have htight : ∀ᵐ v ∂η 2, PhysicalPrimal.charge Y v = 1 := by
      simpa only [hYeq] using htight 2
    rw [integral_congr_ae htight]
    simp only [integral_const, smul_eq_mul, mul_one]
  have hslack : (∫ p, 1 - Y p ∂ρ) = 0 := by
    rw [integral_sub (integrable_const 1) hYρ, integral_const, smul_eq_mul, mul_one,
      hρmass]
    change (∫ v, PhysicalPrimal.charge Y v ∂η 2) = (∫ p, Y p ∂ρ) / 2 at hcharge
    linarith
  have hzero := (integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall (fun p => sub_nonneg.mpr (hY1 p)))
    ((integrable_const 1).sub hYρ)).mp hslack
  have hconull : T =ᵐ[ρ] univ := by
    filter_upwards [hzero] with p hp
    change 1 - Y p = 0 at hp
    exact propext ⟨fun _ => mem_univ p, fun _ => by change Y p = 1; linarith⟩
  have hρsat : ρ.real univ ≤ (μ.prod μ).real T := by
    rw [measureReal_def, ← measure_congr hconull, measureReal_def]
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    rw [← hsatmass]
    exact hρdom T
  change (3 * c - d) / 2 ≤ (μ.prod μ).real T / 2
  rw [hρmass] at hρsat
  linarith

end Erdos1017.CappedModel
