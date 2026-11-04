module

public import Erdos1017.Multipartite.MultipartiteCountableIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Unit-edge mass from near-optimal partitions

The unit-edge consequence of exact near-optimal physical partitions.
All finite clique orders are retained, and physical primal attainment is
not assumed. The fixed-moment profile surgery is not part of this module.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Erdos1017.PhysicalPrimal

variable {V : Type*} [MeasurableSpace V]

theorem orderOccupation_mass (n : ℕ) (μ : Measure (Fin n → V))
    [IsFiniteMeasure μ] :
    (orderOccupation n μ).real Set.univ =
      (Fintype.card (PairIndex n) : ℝ) * μ.real Set.univ := by
  classical
  have hm (ij : PairIndex n) : Measurable (fun v : Fin n → V =>
      (v ij.val.1, v ij.val.2)) :=
    (measurable_pi_apply _).prodMk (measurable_pi_apply _)
  unfold orderOccupation
  simp only [measureReal_def]
  rw [Measure.finsetSum_apply]
  simp only [Measure.map_apply (hm _) MeasurableSet.univ, Set.preimage_univ,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [ENNReal.toReal_mul]
  simp only [ENNReal.toReal_natCast]

private theorem six_le_card_pairIndex {n : ℕ} (hn : 3 ≤ n) :
    6 ≤ Fintype.card (PairIndex n) := by
  let f : PairIndex 3 → PairIndex n := fun ij =>
    ⟨(Fin.castLE hn ij.val.1, Fin.castLE hn ij.val.2), by
      intro h
      exact ij.property (Fin.castLE_injective hn h)⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply Prod.ext
    · exact Fin.castLE_injective hn (congrArg (fun k : PairIndex n => k.val.1) hij)
    · exact Fin.castLE_injective hn (congrArg (fun k : PairIndex n => k.val.2) hij)
  exact (show Fintype.card (PairIndex 3) = 6 by decide) ▸ Fintype.card_le_of_injective f hf

/-- Exact pair balance bounds the mass of all orders above two by their
three-edge minimum, without any bound on the clique order. -/
theorem three_cost_le_pair_mass (μ : Laws V) [∀ n, IsFiniteMeasure (μ n)]
    (Λ : Measure (V × V)) [IsFiniteMeasure Λ]
    (hzero : μ 0 = 0) (hone : μ 1 = 0) (hbalance : occupation μ = Λ) :
    3 * cost μ ≤ Λ.real Set.univ / 2 + 2 * (μ 2).real Set.univ := by
  have hi : Integrable (fun _ : V × V => (1 : ℝ))
      (Measure.sum (fun n => orderOccupation n (μ n))) := by
    change Integrable _ (occupation μ)
    rw [hbalance]
    exact integrable_const 1
  have hs : Summable (fun n => (orderOccupation n (μ n)).real Set.univ) := by
    simpa using hi.summable_integral
  have hc := summable_mass_of_balance μ Λ hzero hone hbalance
  have hm : Λ.real Set.univ = ∑' n, (orderOccupation n (μ n)).real Set.univ := by
    simpa only [integral_const, smul_eq_mul, mul_one, ← hbalance, occupation] using
      integral_sum_measure hi
  have htwo : Summable (fun n : ℕ => if n = 2 then 2 * (μ 2).real Set.univ else 0) :=
    summable_of_ne_finset_zero (s := {2}) (by intro n hn; simp_all)
  have hle (n : ℕ) :
      3 * (μ n).real Set.univ ≤ (orderOccupation n (μ n)).real Set.univ / 2 +
        (if n = 2 then 2 * (μ 2).real Set.univ else 0) := by
    by_cases hn0 : n = 0
    · subst n
      simp [hzero]
    by_cases hn1 : n = 1
    · subst n
      simp [hone]
    by_cases hn2 : n = 2
    · subst n
      rw [orderOccupation_mass]
      norm_num [show Fintype.card (PairIndex 2) = 2 by decide]
      linarith
    have hn : 3 ≤ n := by omega
    have hcard : (6 : ℝ) ≤ Fintype.card (PairIndex n) := by
      exact_mod_cast six_le_card_pairIndex hn
    rw [orderOccupation_mass, ite_eq_right hn2]
    have hm0 : 0 ≤ (μ n).real Set.univ := ENNReal.toReal_nonneg
    nlinarith [mul_le_mul_of_nonneg_right hcard hm0]
  have hsum := (hc.mul_left 3).tsum_le_tsum hle ((hs.div_const 2).add htwo)
  rw [(hs.div_const 2).tsum_add htwo, tsum_div_const, tsum_ite_eq,
    ← hm, tsum_mul_left] at hsum
  exact hsum

/-- Every individual order's nonnegative integrated slack is bounded by
the full primal-dual gap, including for infinitely many occupied orders. -/
theorem integral_slack_le_gap (μ : Laws V) [∀ n, IsFiniteMeasure (μ n)]
    (Λ : Measure (V × V)) [IsFiniteMeasure Λ] (Y : V × V → ℝ)
    (hzero : μ 0 = 0) (hone : μ 1 = 0) (hbalance : occupation μ = Λ)
    (hY : Integrable Y Λ) (htest : ∀ n, ∀ᵐ v ∂μ n, charge Y v ≤ 1) (n : ℕ) :
    (μ n).real Set.univ - (∫ z, Y z ∂orderOccupation n (μ n)) / 2 ≤
      cost μ - (∫ z, Y z ∂Λ) / 2 := by
  have hi : Integrable Y (Measure.sum (fun n => orderOccupation n (μ n))) := by
    change Integrable Y (occupation μ)
    rw [hbalance]
    exact hY
  have horder (k : ℕ) : Integrable Y (orderOccupation k (μ k)) :=
    hi.mono_measure (Measure.le_sum (fun n => orderOccupation n (μ n)) k)
  have hcharge (k : ℕ) := integral_charge k (μ k) Y (horder k)
  have hc := summable_mass_of_balance μ Λ hzero hone hbalance
  have hq : Summable (fun k => ∫ v, charge Y v ∂μ k) := by
    convert (hasSum_integral_measure hi).summable.div_const 2 using 1
    funext k
    exact (hcharge k).2
  have hnonneg (k : ℕ) : 0 ≤ (μ k).real Set.univ - ∫ v, charge Y v ∂μ k := by
    have h := integral_mono_ae (hcharge k).1 (integrable_const (1 : ℝ)) (htest k)
    simpa only [integral_const, smul_eq_mul, mul_one] using sub_nonneg.mpr h
  have hsum : (∑' k, ((μ k).real Set.univ - ∫ v, charge Y v ∂μ k)) =
      cost μ - (∫ z, Y z ∂Λ) / 2 := by
    rw [hc.tsum_sub hq]
    unfold cost
    congr 1
    calc
      (∑' k, ∫ v, charge Y v ∂μ k) =
          ∑' k, (∫ z, Y z ∂orderOccupation k (μ k)) / 2 :=
        tsum_congr (fun k => (hcharge k).2)
      _ = (∫ z, Y z ∂Λ) / 2 := by
        rw [tsum_div_const, ← integral_sum_measure hi]
        change (∫ z, Y z ∂occupation μ) / 2 = _
        rw [hbalance]
  have hsingle := (hc.sub hq).le_tsum n (fun k _ => hnonneg k)
  rw [hsum] at hsingle
  rw [(hcharge n).2] at hsingle
  exact hsingle

/-- Near-unit edge demand is forced by the order-two parent mass and its
integrated slack. Ordered occupations retain the exact factor of two. -/
theorem threshold_mass_lower_bound_of_balance (μ : Laws V)
    [∀ n, IsFiniteMeasure (μ n)] (Λ : Measure (V × V)) [IsFiniteMeasure Λ]
    (Y : V × V → ℝ) (hYm : Measurable Y) (hY : Integrable Y Λ)
    (hcap : ∀ z, Y z ≤ 1) (hzero : μ 0 = 0) (hone : μ 1 = 0)
    (hbalance : occupation μ = Λ) (htest : ∀ n, ∀ᵐ v ∂μ n, charge Y v ≤ 1)
    (ζ : ℝ) (hζ : 0 < ζ) :
    3 * cost μ - Λ.real Set.univ / 2 -
        2 * (cost μ - (∫ z, Y z ∂Λ) / 2) / ζ ≤
      Λ.real {z | 1 - ζ < Y z} := by
  let ρ := orderOccupation 2 (μ 2)
  have hρ : ρ ≤ Λ := by
    rw [← hbalance]
    exact Measure.le_sum (fun n => orderOccupation n (μ n)) 2
  have : IsFiniteMeasure ρ := isFiniteMeasure_of_le Λ hρ
  have hi := hY.mono_measure hρ
  have hs : Integrable (fun z => 1 - Y z) ρ := (integrable_const 1).sub hi
  have hb : MeasurableSet {z | Y z ≤ 1 - ζ} := measurableSet_le hYm measurable_const
  have hmarkov := setIntegral_ge_of_const_le_real (μ := ρ) hb (measure_ne_top _ _)
    (f := fun z => 1 - Y z) (c := ζ) (by intro z hz; dsimp at hz ⊢; linarith)
    hs.integrableOn
  have hnonneg : 0 ≤ᵐ[ρ] (fun z => 1 - Y z) :=
    Filter.Eventually.of_forall (fun z => sub_nonneg.mpr (hcap z))
  have hrestrict := setIntegral_le_integral (s := {z | Y z ≤ 1 - ζ}) hs hnonneg
  have hslack := integral_slack_le_gap μ Λ Y hzero hone hbalance hY htest 2
  have hm : ρ.real Set.univ = 2 * (μ 2).real Set.univ := by
    rw [show ρ = orderOccupation 2 (μ 2) from rfl, orderOccupation_mass]
    norm_num [show Fintype.card (PairIndex 2) = 2 by decide]
  have hslack' : (∫ z, 1 - Y z ∂ρ) ≤
      2 * (cost μ - (∫ z, Y z ∂Λ) / 2) := by
    rw [integral_sub (integrable_const 1) hi, integral_const, smul_eq_mul, mul_one, hm]
    change (μ 2).real Set.univ - (∫ z, Y z ∂ρ) / 2 ≤ _ at hslack
    linarith
  have hbad : ρ.real {z | Y z ≤ 1 - ζ} ≤
      2 * (cost μ - (∫ z, Y z ∂Λ) / 2) / ζ := by
    apply (le_div_iff₀ hζ).mpr
    nlinarith
  have hgood : ρ.real {z | 1 - ζ < Y z} =
      ρ.real Set.univ - ρ.real {z | Y z ≤ 1 - ζ} := by
    simpa only [Set.compl_ofPred, not_le] using measureReal_compl (μ := ρ) hb
  have hle : ρ.real {z | 1 - ζ < Y z} ≤ Λ.real {z | 1 - ζ < Y z} :=
    ENNReal.toReal_mono (measure_ne_top _ _) (hρ _)
  rw [hgood, hm] at hle
  have hmass := three_cost_le_pair_mass μ Λ hzero hone hbalance
  linarith

/-- Arbitrarily near-optimal exact laws force the same lower bound at every
positive charge threshold. No physical primal optimizer is used. -/
theorem threshold_mass_lower_bound_of_near_optimal (A : V → V → Prop)
    (Λ : Measure (V × V)) [IsFiniteMeasure Λ] (Y : V × V → ℝ)
    (hYm : Measurable Y) (hY : Integrable Y Λ) (hcap : ∀ z, Y z ≤ 1)
    (htest : ∀ n (v : Fin n → V),
      (∀ i j, i ≠ j → A (v i) (v j)) → charge Y v ≤ 1)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ μ : Laws V,
      (∀ n, IsFiniteMeasure (μ n)) ∧ Feasible A Λ μ ∧
        cost μ < (∫ z, Y z ∂Λ) / 2 + ε)
    (ζ : ℝ) (hζ : 0 < ζ) :
    3 * ((∫ z, Y z ∂Λ) / 2) - Λ.real Set.univ / 2 ≤
      Λ.real {z | 1 - ζ < Y z} := by
  apply le_of_forall_pos_lt_add
  intro ε hε
  obtain ⟨μ, hf, hμ, hc⟩ := happrox (ε * ζ / 2) (by positivity)
  let (n : ℕ) : IsFiniteMeasure (μ n) := hf n
  have ht (n : ℕ) : ∀ᵐ v ∂μ n, charge Y v ≤ 1 := by
    filter_upwards [hμ.2.2.1 n] with v hv
    exact htest n v hv
  have hweak := weak_duality μ Y Λ hμ.2.2.2 hY
    (summable_mass_of_balance μ Λ hμ.1 hμ.2.1 hμ.2.2.2) ht
  have hthreshold := threshold_mass_lower_bound_of_balance μ Λ Y hYm hY hcap
    hμ.1 hμ.2.1 hμ.2.2.2 ht ζ hζ
  have hgap : 2 * (cost μ - (∫ z, Y z ∂Λ) / 2) / ζ < ε := by
    apply (div_lt_iff₀ hζ).mpr
    nlinarith
  linarith

/-- Exact unrestricted near-optimal partitions force positive measure of
unit-charge edges whenever their dual value exceeds one third of edge mass.
The demand is ordered: its total edge mass is `Λ.real univ / 2`. -/
theorem unit_edge_mass_lower_bound (A : V → V → Prop)
    (Λ : Measure (V × V)) [IsFiniteMeasure Λ] (Y : V × V → ℝ)
    (hYm : Measurable Y) (hY : Integrable Y Λ) (hcap : ∀ z, Y z ≤ 1)
    (htest : ∀ n (v : Fin n → V),
      (∀ i j, i ≠ j → A (v i) (v j)) → charge Y v ≤ 1)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ μ : Laws V,
      (∀ n, IsFiniteMeasure (μ n)) ∧ Feasible A Λ μ ∧
        cost μ < (∫ z, Y z ∂Λ) / 2 + ε) :
    3 * ((∫ z, Y z ∂Λ) / 2) - Λ.real Set.univ / 2 ≤
      Λ.real {z | Y z = 1} := by
  let S : ℕ → Set (V × V) := fun n => {z | 1 - 1 / ((n : ℝ) + 1) < Y z}
  have hSm (n : ℕ) : MeasurableSet (S n) :=
    measurableSet_lt measurable_const hYm
  have hSanti : Antitone S := by
    intro i j hij z hz
    have hrecip : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
    change 1 - 1 / ((j : ℝ) + 1) < Y z at hz
    change 1 - 1 / ((i : ℝ) + 1) < Y z
    linarith
  have hinter : (⋂ n, S n) = {z | Y z = 1} := by
    ext z
    constructor
    · intro hz
      have hz' : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 1) ≤ Y z := by
        intro n
        exact (Set.mem_iInter.mp hz n).le
      have hlim : Filter.Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 1))
          Filter.atTop (nhds (1 : ℝ)) := by
        simpa using tendsto_const_nhds.sub
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      exact le_antisymm (hcap z) (le_of_tendsto hlim (Filter.Eventually.of_forall hz'))
    · intro hz
      apply Set.mem_iInter.mpr
      intro n
      change 1 - 1 / ((n : ℝ) + 1) < Y z
      rw [hz]
      have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  have hlim := tendsto_measure_iInter_atTop (μ := Λ)
    (fun n => (hSm n).nullMeasurableSet) hSanti ⟨0, measure_ne_top _ _⟩
  have hreal := (ENNReal.tendsto_toReal (measure_ne_top Λ (⋂ n, S n))).comp hlim
  rw [hinter] at hreal
  apply ge_of_tendsto hreal
  exact Filter.Eventually.of_forall fun n =>
    threshold_mass_lower_bound_of_near_optimal A Λ Y hYm hY hcap htest happrox
      (1 / ((n : ℝ) + 1)) (by positivity)

end Erdos1017.PhysicalPrimal

namespace Erdos1017.MultipartiteCountableMeasure

local instance : MeasurableSpace Label := ⊤

variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableEq Ω]

/-- The unit-edge bound applies to the actual countable multipartite demand
and every attained homogeneous dual, using unrestricted near-optimal laws. -/
theorem unit_edge_mass_lower_bound (ν : Measure Ω) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] {L : ℝ} {x : MultipartiteProfiles.Profile}
    (hx : x ∈ MultipartiteProfiles.space L) {D : MultipartiteCountableDual.Coefficients}
    (hD : D ∈ MultipartiteCountableDual.feasible)
    (hopt : MultipartiteCountableDual.objective x.2 (MultipartiteProfiles.dust x) D =
      MultipartiteProfiles.limitValue x) :
    let Λ := PhysicalPrimal.graphDemand
      (vertexMeasure ν x.2 (MultipartiteProfiles.dust x)) edgeSet
    3 * MultipartiteProfiles.limitValue x - Λ.real Set.univ / 2 ≤
      Λ.real {z | physicalKernel D z = 1} := by
  let Λ := PhysicalPrimal.graphDemand
    (vertexMeasure ν x.2 (MultipartiteProfiles.dust x)) edgeSet
  have := vertexMeasure_finite ν x.2 (MultipartiteProfiles.atoms_summable hx)
    (MultipartiteProfiles.dust x)
  have : IsFiniteMeasure Λ := by dsimp only [Λ, PhysicalPrimal.graphDemand]; infer_instance
  have hobj : (∫ z, physicalKernel D z ∂Λ) / 2 = MultipartiteProfiles.limitValue x := by
    rw [show Λ = PhysicalPrimal.graphDemand
      (vertexMeasure ν x.2 (MultipartiteProfiles.dust x)) edgeSet from rfl,
      integral_kernel ν x.2 hx.1.1.2 (MultipartiteProfiles.atoms_summable hx)
        (MultipartiteProfiles.dust x) (MultipartiteProfiles.dust_nonneg hx) hD, hopt]
  have hcap (z : (Label × Ω) × (Label × Ω)) : physicalKernel D z ≤ 1 :=
    (le_abs_self _).trans (by
      simpa only [Real.norm_eq_abs, physicalKernel] using norm_kernel_le_one hD z.1.1 z.2.1)
  have happrox (ε : ℝ) (hε : 0 < ε) : ∃ μ : PhysicalPrimal.Laws (Label × Ω),
      (∀ n, IsFiniteMeasure (μ n)) ∧
        PhysicalPrimal.Feasible (fun a b => (a, b) ∈ edgeSet) Λ μ ∧
          PhysicalPrimal.cost μ < (∫ z, physicalKernel D z ∂Λ) / 2 + ε := by
    obtain ⟨μ, hf, hμ, hc⟩ := exists_partition_near_limit ν hx ε hε
    exact ⟨μ, hf, hμ, by simpa only [hobj] using hc⟩
  have h := PhysicalPrimal.unit_edge_mass_lower_bound
    (fun a b => (a, b) ∈ edgeSet) Λ (physicalKernel D)
    (physicalKernel_measurable D) (physicalKernel_integrable hD Λ) hcap
    (fun _ v hv => physical_clique_test hD v hv) happrox
  simpa only [hobj] using h

end Erdos1017.MultipartiteCountableMeasure
