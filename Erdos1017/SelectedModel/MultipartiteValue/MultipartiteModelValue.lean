module

public import Erdos1017.SelectedModel.MultipartiteValue.MultipartiteComponentDemand
public import Erdos1017.SelectedModel.MultipartiteValue.MultipartiteRawPhysicalUpper
public import Erdos1017.SelectedModel.PhysicalPrimal.PhysicalCliqueRepresentative
public import Erdos1017.SelectedModel.Capped.CappedPhysicalRepresentative
public import Erdos1017.Models.Capped.CappedAveraging
public import Erdos1017.Models.Capped.CappedShiftedSelection
public import Erdos1017.LowerBound.FractionalLimitEndpoints

/-!
# A multipartite model is bounded by its own part masses

A fully feasible decorated model with multipartite adjacency has objective at
most the countable multipartite value of its own part masses, at the density of
the same anchor-normalized profile, hence at most the square of its largest
independent part.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1017.MultipartiteModelValue

open MultipartiteComponentRealization

local instance modelValueLabelMeasurable : MeasurableSpace Label := ⊤

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]

/-- Actual bounded scalar clique tests on a multipartite support are bounded
by that partition's own countable multipartite value. Signed charges are allowed. -/
theorem scalar_objective_le_value (q : Ω → Label) (hq : Measurable q)
    (ha : 0 < anchor (μ := μ) q)
    (hmax : ∀ i, mass (μ := μ) q (.inl (some i)) ≤ anchor (μ := μ) q)
    (G : Ω × Ω → Bool) (Y : Ω × Ω → ℝ) (hG : Measurable G) (hY : Measurable Y)
    (b : ℝ) (hb : 0 ≤ b) (hbound : ∀ p, |Y p| ≤ b)
    (hzero : ∀ p, G p = false → Y p = 0)
    (hsupport : ∀ᵐ p ∂μ.prod μ, G p = true ↔ p ∈ partitionEdges q)
    (htests : ∀ n, 2 ≤ n → ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ),
      PhysicalCliqueRepresentative.Clique G v → PhysicalPrimal.charge Y v ≤ 1) :
    (∫ p, Y p ∂μ.prod μ) / 2 ≤ (anchor (μ := μ) q) ^ 2 *
      MultipartiteCountableDual.value (heads (μ := μ) q) (dust (μ := μ) q) := by
  let a := anchor (μ := μ) q
  let c := (ENNReal.ofReal a)⁻¹ * (ENNReal.ofReal a)⁻¹
  have hc : c ≠ ⊤ := by
    dsimp [c]
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr ha)))
      (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr ha)))
  have hcval : c.toReal = 1 / a ^ 2 := by
    have ha' : 0 ≤ a := ha.le
    simp only [c, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal ha']
    ring
  have hE := partitionEdges_measurable q hq
  have hYint : Integrable Y (μ.prod μ) :=
    Integrable.of_bound hY.aestronglyMeasurable b
      (Filter.Eventually.of_forall (fun p => by simpa only [Real.norm_eq_abs] using hbound p))
  have hYe : (∫ p, Y p ∂PhysicalPrimal.graphDemand μ (partitionEdges q)) =
      ∫ p, Y p ∂μ.prod μ := by
    rw [PhysicalPrimal.graphDemand, ← integral_indicator hE]
    apply integral_congr_ae
    filter_upwards [hsupport] with p hp
    by_cases he : p ∈ partitionEdges q
    · exact Set.indicator_of_mem he _
    · have hg : G p = false := Bool.eq_false_iff.mpr (fun hg => he (hp.mp hg))
      simp only [Set.indicator_of_notMem he, hzero p hg]
  have hGe : ∀ᵐ p ∂c • PhysicalPrimal.graphDemand μ (partitionEdges q), G p = true := by
    apply Measure.smul_absolutelyContinuous.ae_le
    apply (ae_restrict_iff' hE).mpr
    filter_upwards [hsupport] with p hp he
    exact hp.mpr he
  have hboundvalue : ((∫ p, Y p ∂μ.prod μ) / 2) / a ^ 2 ≤
      MultipartiteCountableDual.value (heads (μ := μ) q) (dust (μ := μ) q) := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨h, hh, hpush, hlabels⟩ := exists_normalized_sampler q hq ha
    obtain ⟨ρ, hρfinite, hρ, hcost⟩ :=
      MultipartiteCountableMeasure.exists_partition_near_countable_value
        (volume : Measure unitInterval) (heads (μ := μ) q) (heads_cube q ha hmax)
        (heads_summable q hq) (dust (μ := μ) q) (dust_nonneg q ha.le) ε hε
    let (n : ℕ) : IsFiniteMeasure (ρ n) := hρfinite n
    let τ := PhysicalPrimal.mapLaws h ρ
    let (n : ℕ) : IsFiniteMeasure (τ n) := PhysicalPrimal.mapLaws_finite h ρ n
    have hbalance : PhysicalPrimal.occupation τ = c •
        PhysicalPrimal.graphDemand μ (partitionEdges q) := by
      rw [PhysicalPrimal.occupation_mapLaws hh, hρ.2.2.2]
      exact map_graphDemand q hq h hh hpush hlabels
    have hdemandAC : c • PhysicalPrimal.graphDemand μ (partitionEdges q) ≪ μ.prod μ :=
      Measure.absolutelyContinuous_restrict.smul_left c
    have hclique (n : ℕ) : ∀ᵐ v ∂τ n, PhysicalCliqueRepresentative.Clique G v :=
      PhysicalPrimal.ae_all_pairs_of_balance τ _ hbalance _ hGe n
    have hlicensed (n : ℕ) : ∀ᵐ v ∂τ n, PhysicalPrimal.charge Y v ≤ 1 := by
      have hpairs (i j : Fin n) (hij : i ≠ j) :
          (τ n).map (fun v => (v i, v j)) ≪ μ.prod μ := by
        apply Measure.AbsolutelyContinuous.trans _ hdemandAC
        apply Measure.absolutelyContinuous_of_le
        rw [← hbalance]
        exact (PhysicalPrimal.pair_le_orderOccupation n (τ n) ⟨(i, j), hij⟩).trans
          (Measure.le_sum (fun n => PhysicalPrimal.orderOccupation n (τ n)) n)
      filter_upwards [hclique n,
        PhysicalCliqueRepresentative.ae_charge_le_of_pair_marginals μ hG hY b hb hbound
          htests (τ n) hpairs] with v hv ht
      exact ht hv
    have h0 : τ 0 = 0 := by simp [τ, PhysicalPrimal.mapLaws, hρ.1]
    have h1 : τ 1 = 0 := by simp [τ, PhysicalPrimal.mapLaws, hρ.2.1]
    have : IsFiniteMeasure (PhysicalPrimal.graphDemand μ (partitionEdges q)) := by
      unfold PhysicalPrimal.graphDemand
      infer_instance
    have : IsFiniteMeasure (c • PhysicalPrimal.graphDemand μ (partitionEdges q)) :=
      Measure.smul_finite _ hc
    have hweak := PhysicalPrimal.weak_duality τ Y _ hbalance
      (hYint.restrict.smul_measure hc)
      (PhysicalPrimal.summable_mass_of_balance τ _ h0 h1 hbalance) hlicensed
    rw [integral_smul_measure, hYe, hcval, smul_eq_mul,
      PhysicalPrimal.cost_mapLaws hh] at hweak
    have heq : (1 / a ^ 2 * ∫ p, Y p ∂μ.prod μ) / 2 =
        ((∫ p, Y p ∂μ.prod μ) / 2) / a ^ 2 := by ring
    rw [heq] at hweak
    exact hweak.trans hcost.le
  simpa only [mul_comm] using (div_le_iff₀ (sq_pos_of_pos ha)).mp hboundvalue

omit [MeasurableSpace Ω] [StandardBorelSpace Ω] [IsProbabilityMeasure μ] [NullSingletonClass μ] in
private theorem charge_eq_tupleCharge {n : ℕ} (Y : Ω → Ω → ℝ) (v : Fin n → Ω) :
    PhysicalPrimal.charge (Function.uncurry Y) v = FiniteArity.tupleCharge Y v := by
  classical
  have hsum : (∑ i : Fin n, ∑ j : Fin n, if i ≠ j then Y (v i) (v j) else 0) =
      ∑ ij : PhysicalPrimal.PairIndex n, Y (v ij.val.1) (v ij.val.2) := by
    rw [← Fintype.sum_prod_type (fun ij : Fin n × Fin n =>
      if ij.1 ≠ ij.2 then Y (v ij.1) (v ij.2) else 0), ← Finset.sum_filter]
    exact Finset.sum_subtype (p := fun ij : Fin n × Fin n => ij.1 ≠ ij.2)
      (Finset.univ.filter (fun ij : Fin n × Fin n => ij.1 ≠ ij.2)) (by simp)
      (fun ij => Y (v ij.1) (v ij.2))
  simp only [ne_eq, ite_not] at hsum
  unfold PhysicalPrimal.charge FiniteArity.tupleCharge FiniteArity.pairCharge FiniteArity.crossSum
  exact congrArg (fun x : ℝ => x / 2) hsum.symm

open CappedModel

/-- A fully feasible decorated model with actual multipartite adjacency is
bounded by the value of its own actual part masses. No multiplier, charge
sign condition, spectral input or physical primal is assumed. -/
theorem objective_le_own_value (W : Model Ω μ) (hW : FullFeasible W)
    (q : Ω → Label) (hq : Measurable q) (ha : 0 < anchor (μ := μ) q)
    (hmax : ∀ i, mass (μ := μ) q (.inl (some i)) ≤ anchor (μ := μ) q)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if q p.1 ≠ q p.2 ∨ q p.1 = .inr () then 1 else 0) :
    objective W ≤ (anchor (μ := μ) q) ^ 2 *
      MultipartiteCountableDual.value (heads (μ := μ) q) (dust (μ := μ) q) := by
  classical
  let V := averaged W
  have hV : FullFeasible V := fun r => feasible_averaged W (hW r)
  have hbinary : ∀ᵐ p ∂μ.prod μ,
      V.moment CappedColor.adjacency p = (if 0 < shiftedMoment V (-4) p then 1 else 0) ∧
      (1 - V.moment CappedColor.adjacency p) * shiftedMoment V (-4) p = 0 := by
    filter_upwards [hsupport] with p hp
    have haV : V.moment CappedColor.adjacency p =
        if q p.1 ≠ q p.2 ∨ q p.1 = .inr () then 1 else 0 := (adjacency_moment_averaged W p).trans hp
    have hlo := neg_three_adjacency_moment_le_charge V p
    have hhi := charge_moment_le_adjacency V p
    by_cases he : q p.1 ≠ q p.2 ∨ q p.1 = .inr ()
    · rw [ite_eq_left he] at haV
      have hpos : 0 < shiftedMoment V (-4) p := by
        rw [shiftedMoment_eq, haV]
        rw [haV] at hlo
        linarith
      simp only [haV, hpos, ↓reduceIte, sub_self, zero_mul, and_self]
    · rw [ite_eq_right he] at haV
      have hy : V.moment CappedColor.charge p = 0 := by
        rw [haV] at hlo hhi
        linarith
      have hz : shiftedMoment V (-4) p = 0 := by rw [shiftedMoment_eq, haV, hy]; ring
      simp only [haV, hz, lt_self_iff_false, ↓reduceIte, mul_zero, and_self]
  have hstrict := hbinary.mono (fun _ hp => hp.1)
  have hdet : ∀ᵐ p ∂μ.prod μ, ∀ᵐ c ∂V.kernel p,
      shiftedColor (-4) c = shiftedMoment V (-4) p := by
    apply shiftedColor_deterministic_of_complementary V (-4)
      (hbinary.mono (fun _ hp => hp.2))
    intro p
    rw [show conditionalCharge V p = conditionalCharge W p from conditionalCharge_averaged W p]
    exact averaged_deterministic W p
  let G := Function.uncurry (PhysicalRepresentative.adjacency V (-4))
  let Y := Function.uncurry (PhysicalRepresentative.charge V (-4))
  have hG : Measurable G := PhysicalRepresentative.measurable_adjacency V (-4)
  have hY : Measurable Y := PhysicalRepresentative.measurable_charge V (-4)
  have hGpart : ∀ᵐ p ∂μ.prod μ, G p = true ↔ p ∈ partitionEdges q := by
    filter_upwards [hsupport, PhysicalRepresentative.adjacency_moment_ae_eq V (-4) hstrict]
      with p hp hrep
    rw [adjacency_moment_averaged W p, hp] at hrep
    change (if q p.1 ≠ q p.2 ∨ q p.1 = .inr () then (1 : ℝ) else 0) =
      (if G p = true then 1 else 0) at hrep
    change G p = true ↔ q p.1 ≠ q p.2 ∨ q p.1 = .inr ()
    by_cases he : q p.1 ≠ q p.2 ∨ q p.1 = .inr () <;> by_cases hg : G p = true
    · exact ⟨fun _ => he, fun _ => hg⟩
    · simp only [he, hg, ↓reduceIte] at hrep
      norm_num at hrep
    · simp only [he, hg, ↓reduceIte] at hrep
      norm_num at hrep
    · exact ⟨fun h => False.elim (hg h), fun h => False.elim (he h)⟩
  have htests : ∀ n, 2 ≤ n → ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ),
      PhysicalCliqueRepresentative.Clique G v → PhysicalPrimal.charge Y v ≤ 1 := by
    intro n _
    filter_upwards [PhysicalRepresentative.full_feasible V hV (-4) hstrict hdet n] with v hv hc
    rw [charge_eq_tupleCharge]
    exact hv hc
  have hbound := scalar_objective_le_value q hq ha hmax G Y hG hY 3 (by norm_num)
    (fun p => PhysicalRepresentative.charge_bound V (-4) p.1 p.2)
    (fun p => PhysicalRepresentative.charge_zero_of_nonedge V (-4) p.1 p.2) hGpart htests
  have heq : (∫ p, Y p ∂μ.prod μ) / 2 = objective W := by
    calc
      _ = objective V := PhysicalRepresentative.objective_eq V (-4) hstrict
      _ = objective W := objective_averaged W
  rwa [heq] at hbound

/-- The original model density is the density of exactly the same
anchor-normalized head and dust masses used in the objective comparison. -/
theorem density_eq_own_profile (W : Model Ω μ) (q : Ω → Label) (hq : Measurable q)
    (ha : 0 < anchor (μ := μ) q)
    (hmax : ∀ i, mass (μ := μ) q (.inl (some i)) ≤ anchor (μ := μ) q)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if q p.1 ≠ q p.2 ∨ q p.1 = .inr () then 1 else 0) :
    density W = (anchor (μ := μ) q) ^ 2 *
      ((dust (μ := μ) q + ∑' i, heads (μ := μ) q i) +
        ((dust (μ := μ) q + ∑' i, heads (μ := μ) q i) ^ 2 -
          ∑' i, (heads (μ := μ) q i) ^ 2) / 2) := by
  have heq : (fun p : Ω × Ω => if q p.1 ≠ q p.2 ∨ q p.1 = .inr () then (1 : ℝ) else 0) =
      (partitionEdges q).indicator (fun _ => 1) := by
    ext p
    simp only [Set.indicator, partitionEdges, mem_ofPred_eq]
    by_cases hp : q p.1 ≠ q p.2 ∨ q p.1 = .inr () <;> simp only [hp, ↓reduceIte]
  rw [density, integral_congr_ae hsupport, heq,
    integral_indicator (partitionEdges_measurable q hq)]
  change (∫ _ : Ω × Ω, (1 : ℝ) ∂PhysicalPrimal.graphDemand μ (partitionEdges q)) / 2 = _
  rw [integral_const, smul_eq_mul, mul_one]
  exact partition_mass_eq_own_profile q hq ha hmax

/-- The own-profile comparison implies the square of the actual largest
independent part, including countably many positive parts and genuine dust. -/
theorem objective_le_anchor_sq (W : Model Ω μ) (hW : FullFeasible W)
    (q : Ω → Label) (hq : Measurable q) (ha : 0 < anchor (μ := μ) q)
    (hmax : ∀ i, mass (μ := μ) q (.inl (some i)) ≤ anchor (μ := μ) q)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if q p.1 ≠ q p.2 ∨ q p.1 = .inr () then 1 else 0) :
    objective W ≤ (anchor (μ := μ) q) ^ 2 := by
  have hp := heads_cube q ha hmax
  exact (objective_le_own_value W hW q hq ha hmax hsupport).trans
    ((mul_le_mul_of_nonneg_left (MultipartiteCountableDual.value_le_one _
      (fun i => (hp i).1) (fun i => (hp i).2) (heads_summable q hq) _
      (dust_nonneg q ha.le)) (sq_nonneg _)).trans_eq (mul_one _))

omit [StandardBorelSpace Ω] [NullSingletonClass μ] in
/-- A fully feasible model supported on genuine pure clique dust has
nonpositive objective. No positive anchor is required at this endpoint. -/
theorem objective_le_zero_of_pure_dust (W : Model Ω μ) (hW : FullFeasible W)
    (hsupport : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p = 1) :
    objective W ≤ 0 := by
  have hd : density W = 1 / 2 := by
    unfold density
    rw [integral_congr_ae hsupport]
    simp
  have h := fullFeasible_objective_le_densityLimit W hW
  rwa [hd, FractionalGraph.densityLimit_half] at h

end Erdos1017.MultipartiteModelValue
