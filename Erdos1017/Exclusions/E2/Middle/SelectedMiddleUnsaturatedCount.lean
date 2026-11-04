module

public import Erdos1017.Exclusions.E2.Middle.MiddleUnsaturatedScalar
public import Erdos1017.SelectedModel.Saturation.SelectedSaturatedPairCapacity
public import Erdos1017.Exclusions.Common.Private.SelectedPrivatePhysicalPrimal
public import Erdos1017.Exclusions.E2.Upper.SelectedE2AtomGuards

/-!
# Parent counts without order-two parents

With no order-two parents, every family of parent events has excess order at
most one third of the exact pair surplus, so a product-null saturated set gives
`3c ≤ d` and bounds the root excess `L_I` of the attained private primal
(`PrivatePhysicalPrimal.rootExcess_le`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators ENNReal

namespace Erdos1017.PhysicalPrimal

variable {V : Type*} [MeasurableSpace V]

/-- Ordered distinct pairs of `Fin n` number `n * n - n`. -/
theorem card_pairIndex (n : ℕ) : Fintype.card (PairIndex n) = n * n - n := by
  classical
  rw [Fintype.card_subtype]
  have hoff : (Finset.univ.filter fun ij : Fin n × Fin n => ij.1 ≠ ij.2) =
      (Finset.univ : Finset (Fin n)).offDiag := by
    ext x
    simp [Finset.mem_offDiag]
  rw [hoff, Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]

/-- With no order-two parents, every family of parent events has total
excess order at most one third of the exact pair surplus. The pointwise
inequality is `3(r-3) <= binom(r,2)-3`, i.e. `(r-3)(r-4)/2 >= 0`. All
finite orders are retained; no joint absolute continuity is assumed. -/
theorem excess_le_of_no_order_two (η : Laws V) [∀ n, IsFiniteMeasure (η n)]
    (Λ : Measure (V × V)) [IsFiniteMeasure Λ]
    (hzero : η 0 = 0) (hone : η 1 = 0) (htwo : η 2 = 0) (hbalance : occupation η = Λ)
    (F : ∀ n, Set (Fin n → V)) :
    Summable (fun n : ℕ => ((n : ℝ) - 3) * (η n).real (F n)) ∧
      0 ≤ ∑' n : ℕ, ((n : ℝ) - 3) * (η n).real (F n) ∧
      3 * ∑' n : ℕ, ((n : ℝ) - 3) * (η n).real (F n) ≤ Λ.real univ / 2 - 3 * cost η := by
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
          (orderOccupation n (η n)).real univ / 2 - 3 * (η n).real univ := by
    have hsmall (h : η n = 0) : 0 ≤ ((n : ℝ) - 3) * (η n).real (F n) ∧
        3 * (((n : ℝ) - 3) * (η n).real (F n)) ≤
          (orderOccupation n (η n)).real univ / 2 - 3 * (η n).real univ := by
      rw [orderOccupation_mass, h]
      simp
    by_cases hn0 : n = 0
    · subst n
      exact hsmall hzero
    by_cases hn1 : n = 1
    · subst n
      exact hsmall hone
    by_cases hn2 : n = 2
    · subst n
      exact hsmall htwo
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
      nlinarith [h1, h2]
  have hR : Summable (fun n => ((orderOccupation n (η n)).real univ / 2 -
      3 * (η n).real univ) / 3) :=
    ((hs.div_const 2).sub (hc.mul_left 3)).div_const 3
  have hsum : Summable (fun n : ℕ => ((n : ℝ) - 3) * (η n).real (F n)) :=
    hR.of_nonneg_of_le (fun n => (hle n).1) (fun n => by linarith [(hle n).2])
  refine ⟨hsum, tsum_nonneg (fun n => (hle n).1), ?_⟩
  have hbound := (hsum.mul_left 3).tsum_le_tsum (fun n => (hle n).2)
    ((hs.div_const 2).sub (hc.mul_left 3))
  rw [tsum_mul_left, (hs.div_const 2).tsum_sub (hc.mul_left 3), tsum_div_const,
    tsum_mul_left, ← hm] at hbound
  exact hbound

end Erdos1017.PhysicalPrimal

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω]
  [StandardBorelSpace Ω] [MeasurableEq Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NullSingletonClass μ] [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {d c m q : ℝ}

section Count

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- With a product-null actual original saturated set, the same attained
physical primal has no order-two parent, so exact pair demand gives
`3c <= d`. -/
theorem FullStationaryClass.three_objective_le_density_of_saturation_null
    (hW : FullStationaryClass d c W m) (hdhalf : d < 1 / 2) (hgap : benchmark d < c)
    (hnull : (μ.prod μ) {p | chargeKernel W p.1 p.2 = 1} = 0) :
    3 * c ≤ d := by
  have hmass := hW.saturated_charge_mass_lower_bound hdhalf hgap
  change (3 * c - d) / 2 ≤ (μ.prod μ).real {p | chargeKernel W p.1 p.2 = 1} / 2 at hmass
  rw [measureReal_def, hnull, ENNReal.toReal_zero] at hmass
  linarith

/-- The actual middle-E2 no-saturation count forces `q > 187/1000`:
`2 pairFloor q = 3B_q - d < 3c - d <= 0`, while the order-two numerator is
positive on the closed interval `[0, 187/1000]`. -/
theorem FullStationaryClass.middle_unsaturated_q_gt
    (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioo (1 / 10 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hgap : benchmark d < c)
    (hnull : (μ.prod μ) {p | chargeKernel W p.1 p.2 = 1} = 0) :
    187 / 1000 < q := by
  have hq' : q ∈ Ioc (0 : ℝ) (2 / 9) := ⟨by linarith [hq.1], by linarith [hq.2]⟩
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := hdq ▸ LowerE2Scalar.contact_density_mem hq'
  have hcount := hW.three_objective_le_density_of_saturation_null hd.2 hgap hnull
  have hfloor := LowerE2Scalar.pairFloor_eq_twoHeadValue (show 0 ≤ q by linarith [hq.1])
  rw [← hdq, ← hvalue] at hfloor
  by_contra hle
  have hpos := MiddleUnsaturatedScalar.pairFloor_pos
    ⟨by linarith [hq.1], le_of_not_gt hle⟩
  linarith

end Count

namespace SelectedHighLowStructure

/-- The actual original saturated set either has positive product mass,
which constructs a saturated whole-fiber pair, or is product-null. -/
theorem saturated_pair_or_saturation_null (S : SelectedHighLowStructure W m)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1) :
    (∃ r u : S.I, S.IsSaturatedAtomPair r u) ∨
      (μ.prod μ) {p | chargeKernel W p.1 p.2 = 1} = 0 := by
  by_cases hnull : (μ.prod μ) {p | chargeKernel W p.1 p.2 = 1} = 0
  · exact Or.inr hnull
  · left
    apply S.exists_saturated_atom_pair_of_positive_mass hW hd hgap hell
    exact ENNReal.toReal_pos hnull (measure_ne_top _ _)

/-- A product-null saturated set excludes every saturated whole-fiber pair. -/
theorem not_saturated_atom_pair_of_saturation_null (S : SelectedHighLowStructure W m)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (hnull : (μ.prod μ) {p | chargeKernel W p.1 p.2 = 1} = 0) (r u : S.I) :
    ¬S.IsSaturatedAtomPair r u := by
  intro hpair
  have heq := hpair.saturated_mass_eq hW hd hgap hell
  rw [measureReal_def, hnull, ENNReal.toReal_zero] at heq
  have hr : 0 < μ.real {x | S.ρ x = r.val} :=
    ENNReal.toReal_pos (S.hfibers r.val r.property).2.1.ne' (measure_ne_top μ _)
  have hu : 0 < μ.real {x | S.ρ x = u.val} :=
    ENNReal.toReal_pos (S.hfibers u.val u.property).2.1.ne' (measure_ne_top μ _)
  nlinarith [mul_pos hr hu]

/-- The original root excess `L_I`: the excess order of the parents meeting
the actual whole root fiber, in the same attained private primal. -/
def PrivatePhysicalPrimal.rootExcess {S : SelectedHighLowStructure W m} {i p : S.I}
    (P : S.PrivatePhysicalPrimal i p c) : ℝ :=
  ∑' n : ℕ, ((n : ℝ) - 3) * (P.laws n).real {v | ∃ j, S.ρ (v j) = i.val}

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- A product-null saturated set leaves no order-two parent in the same
attained private primal: its tight order-two pair law would be supported
on the null saturated set. -/
theorem PrivatePhysicalPrimal.laws_two_eq_zero {S : SelectedHighLowStructure W m}
    {i p : S.I} (P : S.PrivatePhysicalPrimal i p c)
    (hnull : (μ.prod μ) {p | chargeKernel W p.1 p.2 = 1} = 0) :
    P.laws 2 = 0 := by
  let : ∀ n, IsFiniteMeasure (P.laws n) := P.finite
  let Y : Ω × Ω → ℝ := Function.uncurry (chargeKernel W)
  let T : Set (Ω × Ω) := {p | chargeKernel W p.1 p.2 = 1}
  let Λ := PhysicalPrimal.graphDemand μ
    {z : Ω × Ω | PhysicalRepresentative.adjacency W m z.1 z.2 = true}
  have hY1 (z : Ω × Ω) : Y z ≤ 1 :=
    (charge_moment_le_adjacency W z).trans (adjacency_moment_mem W z).2
  have hdom : Λ ≤ μ.prod μ := Measure.restrict_le_self
  let ρ := PhysicalPrimal.orderOccupation 2 (P.laws 2)
  have hρdom : ρ ≤ Λ :=
    calc
      ρ ≤ PhysicalPrimal.occupation P.laws :=
        Measure.le_sum (fun n => PhysicalPrimal.orderOccupation n (P.laws n)) 2
      _ = Λ := P.feasible.2.2.2
  let : IsFiniteMeasure ρ := isFiniteMeasure_of_le (μ.prod μ) (hρdom.trans hdom)
  have hρmass : ρ.real univ = 2 * (P.laws 2).real univ := by
    rw [show ρ = PhysicalPrimal.orderOccupation 2 (P.laws 2) from rfl,
      PhysicalPrimal.orderOccupation_mass]
    norm_num [show Fintype.card (PhysicalPrimal.PairIndex 2) = 2 by decide]
  have hYi : Integrable Y (μ.prod μ) :=
    Integrable.of_bound (chargeKernel_measurable W) 3 (chargeKernel_bound W)
  have hYρ : Integrable Y ρ := hYi.mono_measure (hρdom.trans hdom)
  have hcharge := (PhysicalPrimal.integral_charge 2 (P.laws 2) Y hYρ).2
  have ht : (∫ v, PhysicalPrimal.charge Y v ∂P.laws 2) = (P.laws 2).real univ := by
    rw [integral_congr_ae (P.tight_original 2)]
    simp only [integral_const, smul_eq_mul, mul_one]
  have hslack : (∫ z, 1 - Y z ∂ρ) = 0 := by
    rw [integral_sub (integrable_const 1) hYρ, integral_const, smul_eq_mul, mul_one, hρmass]
    change (∫ v, PhysicalPrimal.charge Y v ∂P.laws 2) = (∫ z, Y z ∂ρ) / 2 at hcharge
    linarith
  have hzero := (integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall (fun z => sub_nonneg.mpr (hY1 z)))
    ((integrable_const 1).sub hYρ)).mp hslack
  have hconull : T =ᵐ[ρ] univ := by
    filter_upwards [hzero] with z hz
    change 1 - Y z = 0 at hz
    exact propext ⟨fun _ => mem_univ z, fun _ => by
      change chargeKernel W z.1 z.2 = 1
      change 1 - chargeKernel W z.1 z.2 = 0 at hz
      linarith⟩
  have hρzero : ρ univ = 0 := by
    rw [← measure_congr hconull]
    exact le_antisymm ((hρdom.trans hdom) T |>.trans_eq hnull) bot_le
  have hreal : (P.laws 2).real univ = 0 := by
    have h := congrArg ENNReal.toReal hρzero
    rw [ENNReal.toReal_zero] at h
    change ρ.real univ = 0 at h
    linarith
  rw [measureReal_def, ENNReal.toReal_eq_zero_iff] at hreal
  rcases hreal with h | h
  · exact Measure.measure_univ_eq_zero.mp h
  · exact absurd h (measure_ne_top _ _)

/-- On a product-null saturated set, the original root excess of the same
attained private primal satisfies `0 <= L_I <= (d - 3c)/3`. -/
theorem PrivatePhysicalPrimal.rootExcess_le {S : SelectedHighLowStructure W m}
    {i p : S.I} (P : S.PrivatePhysicalPrimal i p c)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hnull : (μ.prod μ) {p | chargeKernel W p.1 p.2 = 1} = 0) :
    0 ≤ P.rootExcess ∧ 3 * P.rootExcess ≤ d - 3 * c := by
  let : ∀ n, IsFiniteMeasure (P.laws n) := P.finite
  let E : Set (Ω × Ω) := {z | PhysicalRepresentative.adjacency W m z.1 z.2 = true}
  let Λ := PhysicalPrimal.graphDemand μ E
  have hE : MeasurableSet E :=
    (PhysicalRepresentative.measurable_adjacency W m) (measurableSet_singleton true)
  let : IsFiniteMeasure Λ := by
    change IsFiniteMeasure ((μ.prod μ).restrict E)
    infer_instance
  have hzero : P.laws 0 = 0 := P.feasible.1
  have hone : P.laws 1 = 0 := P.feasible.2.1
  have htwo := P.laws_two_eq_zero hnull
  obtain ⟨_, hnonneg, hbound⟩ := PhysicalPrimal.excess_le_of_no_order_two P.laws Λ
    hzero hone htwo P.feasible.2.2.2 (fun _ => {v | ∃ j, S.ρ (v j) = i.val})
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
  exact ⟨hnonneg, by unfold PrivatePhysicalPrimal.rootExcess; linarith⟩

end SelectedHighLowStructure

end Erdos1017.CappedModel
