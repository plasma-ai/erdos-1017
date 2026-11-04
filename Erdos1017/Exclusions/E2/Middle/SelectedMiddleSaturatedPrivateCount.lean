module

public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleUnsaturatedCount
public import Erdos1017.Exclusions.Common.Private.SelectedPrivateRootIncidence

/-!
# Order-two correction of the private root excess

The order-two stock contributes twice its mass to the pair surplus, the selected
private peak has no order-two root parent, and the all-order peak excess is paid
by the saturated partner stock and turned into the coupled pair-floor reserve
(`rootExcess_lt_pair_floor_reserve`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators ENNReal

namespace Erdos1017.PhysicalPrimal

variable {V : Type*} [MeasurableSpace V]

/-- The order-two stock contributes twice its mass to the pair surplus.
The selected root has no order-two parent incidence, while every higher
order is retained in the same law. -/
theorem excess_le_with_order_two (η : Laws V) [∀ n, IsFiniteMeasure (η n)]
    (Λ : Measure (V × V)) [IsFiniteMeasure Λ]
    (hzero : η 0 = 0) (hone : η 1 = 0) (hbalance : occupation η = Λ)
    (F : ∀ n, Set (Fin n → V)) (hFtwo : (η 2).real (F 2) = 0) :
    Summable (fun n : ℕ => ((n : ℝ) - 3) * (η n).real (F n)) ∧
      0 ≤ ∑' n : ℕ, ((n : ℝ) - 3) * (η n).real (F n) ∧
      3 * ∑' n : ℕ, ((n : ℝ) - 3) * (η n).real (F n) ≤
        Λ.real univ / 2 - 3 * cost η + 2 * (η 2).real univ := by
  have hi : Integrable (fun _ : V × V => (1 : ℝ))
      (Measure.sum (fun n => orderOccupation n (η n))) := by
    change Integrable _ (occupation η)
    rw [hbalance]
    exact integrable_const 1
  have hs : Summable (fun n => (orderOccupation n (η n)).real univ) := by
    simpa using hi.summable_integral
  have hc := summable_mass_of_balance η Λ hzero hone hbalance
  have hm : Λ.real univ = ∑' n, (orderOccupation n (η n)).real univ := by
    simpa only [integral_const, smul_eq_mul, mul_one, ← hbalance, occupation] using
      integral_sum_measure hi
  have hle (n : ℕ) :
      0 ≤ ((n : ℝ) - 3) * (η n).real (F n) ∧
        3 * (((n : ℝ) - 3) * (η n).real (F n)) ≤
          (orderOccupation n (η n)).real univ / 2 -
            3 * (η n).real univ +
            (if n = 2 then 2 * (η 2).real univ else 0) := by
    have hsmall (h : η n = 0) (hn : n ≠ 2) :
        0 ≤ ((n : ℝ) - 3) * (η n).real (F n) ∧
          3 * (((n : ℝ) - 3) * (η n).real (F n)) ≤
            (orderOccupation n (η n)).real univ / 2 -
              3 * (η n).real univ +
              (if n = 2 then 2 * (η 2).real univ else 0) := by
      rw [orderOccupation_mass, h]
      simp [hn]
    by_cases hn0 : n = 0
    · subst n
      exact hsmall hzero (by decide)
    by_cases hn1 : n = 1
    · subst n
      exact hsmall hone (by decide)
    by_cases hn2 : n = 2
    · subst n
      rw [hFtwo, orderOccupation_mass]
      norm_num [show Fintype.card (PairIndex 2) = 2 by decide]
      linarith
    have hn : 3 ≤ n := by omega
    have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hcard : (Fintype.card (PairIndex n) : ℝ) = (n : ℝ) * n - n := by
      rw [card_pairIndex, Nat.cast_sub (Nat.le_mul_self n), Nat.cast_mul]
    have hquad : 0 ≤ ((n : ℝ) - 3) * ((n : ℝ) - 4) := by
      by_cases h3 : n = 3
      · subst n
        norm_num
      · have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast (show 4 ≤ n by omega)
        exact mul_nonneg (by linarith) (by linarith)
    have hF : (η n).real (F n) ≤ (η n).real univ := measureReal_mono (subset_univ _)
    have hF0 : 0 ≤ (η n).real (F n) := measureReal_nonneg
    have ha0 : 0 ≤ (η n).real univ := measureReal_nonneg
    rw [orderOccupation_mass, hcard]
    constructor
    · exact mul_nonneg (by linarith) hF0
    · have h1 := mul_le_mul_of_nonneg_left hF (show 0 ≤ (n : ℝ) - 3 by linarith)
      have h2 := mul_nonneg hquad ha0
      simp only [ite_eq_right hn2]
      nlinarith [h1, h2]
  have htwo : Summable (fun n : ℕ =>
      if n = 2 then 2 * (η 2).real univ else 0) :=
    summable_of_ne_finset_zero (s := {2}) (by intro n hn; simp_all)
  have hR : Summable (fun n => ((orderOccupation n (η n)).real univ / 2 -
      3 * (η n).real univ +
        (if n = 2 then 2 * (η 2).real univ else 0)) / 3) := by
    apply Summable.div_const
    exact ((hs.div_const 2).sub (hc.mul_left 3)).add htwo
  have hsum : Summable (fun n : ℕ => ((n : ℝ) - 3) * (η n).real (F n)) :=
    hR.of_nonneg_of_le (fun n => (hle n).1) (fun n => by linarith [(hle n).2])
  refine ⟨hsum, tsum_nonneg (fun n => (hle n).1), ?_⟩
  have hbound := (hsum.mul_left 3).tsum_le_tsum (fun n => (hle n).2)
    (((hs.div_const 2).sub (hc.mul_left 3)).add htwo)
  rw [((hs.div_const 2).sub (hc.mul_left 3)).tsum_add htwo,
    (hs.div_const 2).tsum_sub (hc.mul_left 3), tsum_div_const,
    tsum_mul_left, tsum_ite_eq] at hbound
  rw [← hm] at hbound
  rw [tsum_mul_left] at hbound
  have hcost : (∑' n, (η n).real univ) = cost η := by
    simp only [cost, measureReal_def]
  rw [hcost] at hbound
  exact hbound

/-- Zero order-two root leaves mean that no order-two parent meets the
selected root, regardless of dependence between its two coordinates. -/
theorem order_two_root_event_null (ρ : Measure (Fin 2 → V))
    (I : Set V) (hI : MeasurableSet I)
    (hzero : orderRootLeaves 2 ρ I = 0) :
    ρ {v | ∃ j : Fin 2, v j ∈ I} = 0 := by
  have hfirst : orderFirstOccupation 2 ρ I = 0 := by
    have h := congrArg (fun σ : Measure V => σ univ) hzero
    rw [orderRootLeaves_mass 2 ρ I hI] at h
    simpa using h
  have hbound : ρ {v | ∃ j : Fin 2, v j ∈ I} ≤
      orderFirstOccupation 2 ρ I := by
    have hcover : {v : Fin 2 → V | ∃ j, v j ∈ I} =
        ⋃ j : Fin 2, {v | v j ∈ I} := by
      ext v
      simp
    rw [hcover]
    have hle := measure_iUnion_le (μ := ρ) (fun j : Fin 2 => {v | v j ∈ I})
    have heq : orderFirstOccupation 2 ρ I =
        ∑ j : Fin 2, ρ {v | v j ∈ I} := by
      rw [orderFirstOccupation, Measure.finsetSum_apply]
      apply Finset.sum_congr rfl
      intro j _
      exact Measure.map_apply (measurable_pi_apply j) hI
    rw [heq]
    simpa only [tsum_fintype] using hle
  rw [hfirst] at hbound
  exact le_antisymm hbound bot_le

end Erdos1017.PhysicalPrimal

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [MeasurableEq Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NullSingletonClass μ] [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}
  {i p : S.I} {c d : ℝ}

/-- Every tight order-two parent uses the unique original saturated
block. Its mass is bounded by the two original atom masses. -/
theorem PrivatePhysicalPrimal.two_mass_le_saturated_stock
    (P : S.PrivatePhysicalPrimal i p c) (q : S.I)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1) (hsat : S.IsSaturatedAtomPair p q) :
    (P.laws 2).real univ ≤
      μ.real {x | S.ρ x = p.val} * μ.real {x | S.ρ x = q.val} := by
  have : IsFiniteMeasure (P.laws 2) := P.finite 2
  let Y : Ω × Ω → ℝ := W.moment CappedColor.charge
  let T : Set (Ω × Ω) := {z | Y z = 1}
  let ρ := PhysicalPrimal.orderOccupation 2 (P.laws 2)
  have hρdom : ρ ≤ μ.prod μ := by
    calc
      ρ ≤ PhysicalPrimal.occupation P.laws :=
        Measure.le_sum (fun n => PhysicalPrimal.orderOccupation n (P.laws n)) 2
      _ = PhysicalPrimal.graphDemand μ
          {z | PhysicalRepresentative.adjacency W m z.1 z.2 = true} :=
        P.feasible.2.2.2
      _ ≤ μ.prod μ := Measure.restrict_le_self
  have : IsFiniteMeasure ρ := isFiniteMeasure_of_le (μ.prod μ) hρdom
  have hρmass : ρ.real univ = 2 * (P.laws 2).real univ := by
    rw [show ρ = PhysicalPrimal.orderOccupation 2 (P.laws 2) from rfl,
      PhysicalPrimal.orderOccupation_mass]
    norm_num [show Fintype.card (PhysicalPrimal.PairIndex 2) = 2 by decide]
  have hYi : Integrable Y (μ.prod μ) :=
    Integrable.of_bound (chargeKernel_measurable W) 3 (chargeKernel_bound W)
  have hYρ : Integrable Y ρ := hYi.mono_measure hρdom
  have hcharge := (PhysicalPrimal.integral_charge 2 (P.laws 2) Y hYρ).2
  have ht : (∫ v, PhysicalPrimal.charge Y v ∂P.laws 2) =
      (P.laws 2).real univ := by
    have hYeq : Function.uncurry (chargeKernel W) = Y := rfl
    have htight : ∀ᵐ v ∂P.laws 2, PhysicalPrimal.charge Y v = 1 := by
      simpa only [hYeq] using P.tight_original 2
    rw [integral_congr_ae htight]
    simp only [integral_const, smul_eq_mul, mul_one]
  have hslack : (∫ z, 1 - Y z ∂ρ) = 0 := by
    rw [integral_sub (integrable_const 1) hYρ, integral_const, smul_eq_mul,
      mul_one, hρmass]
    change (∫ v, PhysicalPrimal.charge Y v ∂P.laws 2) =
      (∫ z, Y z ∂ρ) / 2 at hcharge
    linarith
  have hzero := (integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall (fun z => sub_nonneg.mpr
      ((charge_moment_le_adjacency W z).trans (adjacency_moment_mem W z).2)))
    ((integrable_const 1).sub hYρ)).mp hslack
  have hconull : T =ᵐ[ρ] univ := by
    filter_upwards [hzero] with z hz
    change 1 - Y z = 0 at hz
    exact propext ⟨fun _ => mem_univ z, fun _ => by
      change Y z = 1
      linarith⟩
  have hρsat : ρ.real univ ≤ (μ.prod μ).real T := by
    rw [measureReal_def, ← measure_congr hconull, measureReal_def]
    exact ENNReal.toReal_mono (measure_ne_top _ _) (hρdom T)
  have hsatmass := hsat.saturated_mass_eq hW hd hgap hell
  change (μ.prod μ).real T =
    2 * μ.real {x | S.ρ x = p.val} * μ.real {x | S.ρ x = q.val} at hsatmass
  rw [hρmass, hsatmass] at hρsat
  linarith

/-- The selected private peak has no order-two root parent. The actual
order-two saturated stock contributes its full correction to the count. -/
theorem PrivatePhysicalPrimal.rootExcess_le_with_order_two
    (P : S.PrivatePhysicalPrimal i p c)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.H) :
    0 ≤ P.rootExcess ∧
      3 * P.rootExcess ≤ d - 3 * c + 2 * (P.laws 2).real univ := by
  let : ∀ n, IsFiniteMeasure (P.laws n) := P.finite
  let E : Set (Ω × Ω) :=
    {z | PhysicalRepresentative.adjacency W m z.1 z.2 = true}
  let Λ := PhysicalPrimal.graphDemand μ E
  have hE : MeasurableSet E :=
    (PhysicalRepresentative.measurable_adjacency W m) (measurableSet_singleton true)
  let : IsFiniteMeasure Λ := by
    change IsFiniteMeasure ((μ.prod μ).restrict E)
    infer_instance
  have hzero : P.laws 0 = 0 := P.feasible.1
  have hone : P.laws 1 = 0 := P.feasible.2.1
  have htwo := P.orderRootLeaves_two_first_eq_zero hW hd hgap hell hhigh
  have hFtwo : (P.laws 2).real
      {v | ∃ j, S.ρ (v j) = i.val} = 0 := by
    have hnull := PhysicalPrimal.order_two_root_event_null (P.laws 2)
      {x | S.ρ x = i.val} (S.hfibers i.val i.property).1 htwo
    have heq : {v : Fin 2 → Ω | ∃ j, S.ρ (v j) = i.val} =
        {v | ∃ j, v j ∈ {x | S.ρ x = i.val}} := by
      ext v
      simp
    rw [measureReal_def, heq, hnull, ENNReal.toReal_zero]
  obtain ⟨_, hnonneg, hbound⟩ :=
    PhysicalPrimal.excess_le_with_order_two P.laws Λ hzero hone
      P.feasible.2.2.2 (fun _ => {v | ∃ j, S.ρ (v j) = i.val}) hFtwo
  have hΛ : Λ.real univ = 2 * d := by
    have hs := (hW.strict_gap_structure hd hgap).strict_support
    have hind : (fun z : Ω × Ω => W.moment CappedColor.adjacency z) =ᵐ[μ.prod μ]
        E.indicator (fun _ => (1 : ℝ)) := by
      filter_upwards [PhysicalRepresentative.adjacency_moment_ae_eq W m hs] with z hz
      rw [hz]
      by_cases hz' : PhysicalRepresentative.adjacency W m z.1 z.2 = true
      · rw [indicator_of_mem (show z ∈ E from hz')]
        simp [hz']
      · rw [indicator_of_notMem (show z ∉ E from hz')]
        simp [hz']
    have hdens := hW.density_eq
    unfold density at hdens
    rw [integral_congr_ae hind, integral_indicator hE, setIntegral_const, smul_eq_mul,
      mul_one] at hdens
    change ((μ.prod μ).restrict E).real univ = 2 * d
    rw [measureReal_def, Measure.restrict_apply MeasurableSet.univ, univ_inter]
    rw [measureReal_def] at hdens
    linarith
  rw [hΛ, P.cost] at hbound
  exact ⟨hnonneg, by
    unfold PrivatePhysicalPrimal.rootExcess
    linarith⟩

/-- The same private primal's all-order peak excess is paid by the
actual saturated partner stock. -/
theorem PrivatePhysicalPrimal.rootExcess_le_saturated_stock
    (P : S.PrivatePhysicalPrimal i p c) (q : S.I)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.H)
    (hsat : S.IsSaturatedAtomPair p q) :
    0 ≤ P.rootExcess ∧
      3 * P.rootExcess ≤ d - 3 * c +
        2 * μ.real {x | S.ρ x = p.val} *
          μ.real {x | S.ρ x = q.val} := by
  have hcount := P.rootExcess_le_with_order_two hW hd hgap hell hhigh
  have hstock := P.two_mass_le_saturated_stock q hW hd hgap hell hsat
  constructor
  · exact hcount.1
  · linarith [hcount.2]

/-- The actual contact value turns the same-law saturated surplus into
the coupled pair-floor reserve, even if that floor is negative. -/
theorem PrivatePhysicalPrimal.rootExcess_lt_pair_floor_reserve
    (P : S.PrivatePhysicalPrimal i p c) (u : S.I) {q : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.H)
    (hsat : S.IsSaturatedAtomPair p u)
    (hq : 0 ≤ q)
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3)) :
    let b := μ.real {x | S.ρ x = p.val}
    let v := μ.real {x | S.ρ x = u.val}
    0 ≤ P.rootExcess ∧
      LowerE2Scalar.pairFloor q < b * v ∧
      3 * P.rootExcess < 2 * (b * v - LowerE2Scalar.pairFloor q) := by
  have hcount := P.rootExcess_le_saturated_stock u hW hd hgap hell hhigh hsat
  have hfloor := LowerE2Scalar.pairFloor_eq_twoHeadValue hq
  rw [← hvalue, ← hdq] at hfloor
  dsimp only
  constructor
  · exact hcount.1
  constructor
  · linarith [hcount.2]
  · linarith [hcount.2]

end Erdos1017.CappedModel.SelectedHighLowStructure
