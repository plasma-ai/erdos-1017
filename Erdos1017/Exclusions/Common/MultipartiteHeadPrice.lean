module

public import Erdos1017.Exclusions.Common.TwoCenter.TwoCenterPhysicalSlack
public import Erdos1017.Exclusions.Common.TwoCenter.TwoCenterHeadPrice
public import Erdos1017.Exclusions.Common.CappedBinaryRepresentative

/-!
# Head prices of a multipartite model

The head law `headLaw`, normalized remainder and head price `headPrice` (the
conditional mean of the charge kernel on one head) are defined along with the
complete multipartite support `partitionAdj`, and a fully feasible multipartite
model pays bare-head slack at its two-head price.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal Classical

namespace Erdos1017.MultipartiteHeadPrice

open PhysicalPrimal PhysicalCliqueRepresentative

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The genuine normalized restriction of the current law to one head. -/
abbrev headLaw (μ : Measure Ω) (I : Set Ω) : Measure Ω := cellLaw μ I

/-- The entire actual remainder is normalized by the common head mass. -/
def normalizedRemainder (μ : Measure Ω) (I J : Set Ω) (t : ℝ) : Measure Ω :=
  (ENNReal.ofReal t)⁻¹ • μ.restrict (I ∪ J)ᶜ

/-- The head price is the current conditional mean of the unchanged charge
kernel, not a coefficient supplied by an optimization certificate. -/
def headPrice (W : CappedModel.Model Ω μ) (I J : Set Ω) : ℝ :=
  ∫ p, CappedModel.chargeKernel W p.1 p.2 ∂(headLaw μ I).prod (headLaw μ J)

/-- Equal actual head masses identify their ENNReal class measures. -/
theorem measure_eq_of_real_mass {I : Set Ω} {t : ℝ} (hI : μ.real I = t) :
    μ I = ENNReal.ofReal t := by
  rw [← hI, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ I)]

/-- The two actual heads and the normalized remainder reconstruct the
entire normalized current vertex measure exactly. -/
theorem normalized_vertices {I J : Set Ω} (hI : MeasurableSet I) (hJ : MeasurableSet J)
    (hdis : Disjoint I J) {t : ℝ} (hmI : μ.real I = t) (hmJ : μ.real J = t) :
    headLaw μ I + headLaw μ J + normalizedRemainder μ I J t = (ENNReal.ofReal t)⁻¹ • μ := by
  rw [headLaw, headLaw, cellLaw, cellLaw, measure_eq_of_real_mass hmI, measure_eq_of_real_mass hmJ,
    normalizedRemainder, ← smul_add, ← smul_add, ← Measure.restrict_union hdis hJ,
    Measure.restrict_add_restrict_compl (hI.union hJ)]

/-- The actual original remainder mass is one minus the two head masses. -/
theorem remainder_mass {I J : Set Ω} (hI : MeasurableSet I) (hJ : MeasurableSet J)
    (hdis : Disjoint I J) {t : ℝ} (hmI : μ.real I = t) (hmJ : μ.real J = t) :
    μ.real (I ∪ J)ᶜ = 1 - 2 * t := by
  have h := measureReal_add_measureReal_compl (μ := μ) (hI.union hJ)
  rw [measureReal_union hdis hJ, hmI, hmJ, probReal_univ] at h
  linarith

/-- Positive head mass makes the actual normalized remainder finite. -/
theorem normalizedRemainder_finite (I J : Set Ω) {t : ℝ} (ht : 0 < t) :
    IsFiniteMeasure (normalizedRemainder μ I J t) :=
  Measure.smul_finite _ (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr ht).ne')

/-- The actual normalized remainder has the exact current mass r/t. -/
theorem normalizedRemainder_mass {I J : Set Ω} (hI : MeasurableSet I) (hJ : MeasurableSet J)
    (hdis : Disjoint I J) {t : ℝ} (ht : 0 < t) (hmI : μ.real I = t) (hmJ : μ.real J = t) :
    (normalizedRemainder μ I J t).real univ = (1 - 2 * t) / t := by
  simp only [normalizedRemainder, measureReal_def, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply_univ, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal ht.le]
  rw [show (μ (I ∪ J)ᶜ).toReal = 1 - 2 * t from remainder_mass hI hJ hdis hmI hmJ]
  ring

/-- At t>1/3 the genuine normalized remainder is a subprobability, allowing
the explicit zero/one/two body construction without approximation. -/
theorem normalizedRemainder_mass_le_one {I J : Set Ω} (hI : MeasurableSet I) (hJ : MeasurableSet J)
    (hdis : Disjoint I J) {t : ℝ} (ht : 1 / 3 < t) (hmI : μ.real I = t) (hmJ : μ.real J = t) :
    normalizedRemainder μ I J t univ ≤ 1 := by
  have htpos : 0 < t := by linarith
  have := normalizedRemainder_finite (μ := μ) I J htpos
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (by norm_num)).mp
  change (normalizedRemainder μ I J t).real univ ≤ 1
  rw [normalizedRemainder_mass hI hJ hdis htpos hmI hmJ]
  exact (div_le_one htpos).mpr (by linarith)

omit [IsProbabilityMeasure μ] in
/-- The actual normalized remainder is absolutely continuous to the
current endpoint probability law. -/
theorem normalizedRemainder_absolutelyContinuous (I J : Set Ω) (t : ℝ) :
    normalizedRemainder μ I J t ≪ μ := Measure.absolutelyContinuous_restrict.smul_left _

omit [IsProbabilityMeasure μ] in
/-- A conditional head sample remains in its own literal original class. -/
theorem ae_mem_headLaw {I : Set Ω} (hI : MeasurableSet I) : ∀ᵐ x ∂headLaw μ I, x ∈ I :=
  Measure.ae_smul_measure (ae_restrict_mem hI) _

omit [IsProbabilityMeasure μ] in
/-- Every normalized remainder sample is outside both actual heads. -/
theorem ae_mem_normalizedRemainder (I J : Set Ω) (hI : MeasurableSet I) (hJ : MeasurableSet J) (t : ℝ) :
    ∀ᵐ x ∂normalizedRemainder μ I J t, x ∈ (I ∪ J)ᶜ :=
  Measure.ae_smul_measure (ae_restrict_mem (hI.union hJ).compl) _


omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- Physical ordered-pair charge equals the finite-arity tuple charge. -/
theorem physicalCharge_eq_tupleCharge {n : ℕ} (Y : Ω → Ω → ℝ) (v : Fin n → Ω) :
    charge (Function.uncurry Y) v = FiniteArity.tupleCharge Y v := by
  classical
  have hsum : (∑ i : Fin n, ∑ j : Fin n, if i ≠ j then Y (v i) (v j) else 0) =
      ∑ ij : PairIndex n, Y (v ij.val.1) (v ij.val.2) := by
    rw [← Fintype.sum_prod_type (fun ij : Fin n × Fin n =>
      if ij.1 ≠ ij.2 then Y (v ij.1) (v ij.2) else 0), ← Finset.sum_filter]
    exact Finset.sum_subtype (p := fun ij : Fin n × Fin n => ij.1 ≠ ij.2)
      (Finset.univ.filter (fun ij : Fin n × Fin n => ij.1 ≠ ij.2)) (by simp)
      (fun ij => Y (v ij.1) (v ij.2))
  simp only [ne_eq, ite_not] at hsum
  unfold charge FiniteArity.tupleCharge FiniteArity.pairCharge
    FiniteArity.crossSum
  exact congrArg (fun x : ℝ => x / 2) hsum.symm

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]

/-- An actual fully tested signed scalar dual with two independent
universal head classes is bounded by its own current conditional head price.
The remainder may be any graph, with no finite or dust approximation. -/
theorem scalar_objective_le_head_price
    (G : Ω × Ω → Bool) (hG : Measurable G) (hGsym : ∀ p, G p.swap = G p)
    (Y : Ω × Ω → ℝ) (hY : Measurable Y) (hYsym : ∀ p, Y p.swap = Y p)
    (b : ℝ) (hb : 0 ≤ b) (hbound : ∀ p, |Y p| ≤ b) (hupper : ∀ p, Y p ≤ 1)
    (hzero : ∀ p, G p = false → Y p = 0)
    (htests : ∀ n, 2 ≤ n → ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ), Clique G v → charge Y v ≤ 1)
    {I J : Set Ω} (hI : MeasurableSet I) (hJ : MeasurableSet J) (hdis : Disjoint I J)
    {t : ℝ} (ht : 1 / 3 < t) (hmI : μ.real I = t) (hmJ : μ.real J = t)
    (hrowI : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → (G p = true ↔ p.2 ∉ I))
    (hrowJ : ∀ᵐ p ∂μ.prod μ, p.1 ∈ J → (G p = true ↔ p.2 ∉ J)) :
    (∫ p, Y p ∂μ.prod μ) / 2 ≤
      t ^ 2 - t * (3 * t - 1) * (1 - ∫ p, Y p ∂(headLaw μ I).prod (headLaw μ J)) := by
  classical
  have htpos : 0 < t := by linarith
  have hI0 : μ I ≠ 0 := by
    intro hz
    rw [measureReal_def, hz, ENNReal.toReal_zero] at hmI
    linarith
  have hJ0 : μ J ≠ 0 := by
    intro hz
    rw [measureReal_def, hz, ENNReal.toReal_zero] at hmJ
    linarith
  let σ₁ := headLaw μ I
  let σ₂ := headLaw μ J
  let η := normalizedRemainder μ I J t
  let E : Set (Ω × Ω) := {p | G p = true}
  let c := (ENNReal.ofReal t)⁻¹ * (ENNReal.ofReal t)⁻¹
  have : IsProbabilityMeasure σ₁ := cellLaw_probability μ I hI0
  have : IsProbabilityMeasure σ₂ := cellLaw_probability μ J hJ0
  have : IsFiniteMeasure η := normalizedRemainder_finite I J htpos
  have hη : η univ ≤ 1 := normalizedRemainder_mass_le_one hI hJ hdis ht hmI hmJ
  have hσ₁ : σ₁ ≪ μ := cellLaw_absolutelyContinuous μ I
  have hσ₂ : σ₂ ≪ μ := cellLaw_absolutelyContinuous μ J
  have hηac : η ≪ μ := normalizedRemainder_absolutelyContinuous I J t
  have hE : MeasurableSet E := hG (measurableSet_singleton true)
  have hEsym : Prod.swap ⁻¹' E = E := by
    ext p
    change G p.swap = true ↔ G p = true
    rw [hGsym]
  have rowI (τ : Measure Ω) [IsFiniteMeasure τ] (hτ : τ ≪ μ) :
      ∀ᵐ p ∂σ₁.prod τ, G p = true ↔ p.2 ∉ I := by
    filter_upwards [(hσ₁.prod hτ).ae_le hrowI,
      Measure.quasiMeasurePreserving_fst.ae (ae_mem_headLaw hI)] with p hp hi
    exact hp hi
  have rowJ (τ : Measure Ω) [IsFiniteMeasure τ] (hτ : τ ≪ μ) :
      ∀ᵐ p ∂σ₂.prod τ, G p = true ↔ p.2 ∉ J := by
    filter_upwards [(hσ₂.prod hτ).ae_le hrowJ,
      Measure.quasiMeasurePreserving_fst.ae (ae_mem_headLaw hJ)] with p hp hj
    exact hp hj
  have h₁₁ : ∀ᵐ p ∂σ₁.prod σ₁, p ∉ E := by
    filter_upwards [rowI σ₁ hσ₁, Measure.quasiMeasurePreserving_snd.ae (ae_mem_headLaw hI)]
      with p hp hi
    exact fun he => (hp.mp he) hi
  have h₂₂ : ∀ᵐ p ∂σ₂.prod σ₂, p ∉ E := by
    filter_upwards [rowJ σ₂ hσ₂, Measure.quasiMeasurePreserving_snd.ae (ae_mem_headLaw hJ)]
      with p hp hj
    exact fun he => (hp.mp he) hj
  have h₁₂ : ∀ᵐ p ∂σ₁.prod σ₂, p ∈ E := by
    filter_upwards [rowI σ₂ hσ₂, Measure.quasiMeasurePreserving_snd.ae (ae_mem_headLaw hJ)]
      with p hp hj
    exact hp.mpr (fun hi => disjoint_left.mp hdis hi hj)
  have h₁R : ∀ᵐ p ∂σ₁.prod η, p ∈ E := by
    filter_upwards [rowI η hηac,
      Measure.quasiMeasurePreserving_snd.ae (ae_mem_normalizedRemainder I J hI hJ t)] with p hp hr
    exact hp.mpr (fun hi => hr (Or.inl hi))
  have h₂R : ∀ᵐ p ∂σ₂.prod η, p ∈ E := by
    filter_upwards [rowJ η hηac,
      Measure.quasiMeasurePreserving_snd.ae (ae_mem_normalizedRemainder I J hI hJ t)] with p hp hr
    exact hp.mpr (fun hj => hr (Or.inr hj))
  let ρ := TwoCenterPhysicalSlack.laws σ₁ σ₂ η E
  have hfeas := TwoCenterPhysicalSlack.laws_feasible σ₁ σ₂ η hη E hE hEsym h₁₁ h₂₂ h₁₂ h₁R h₂R
  have hvertices : σ₁ + σ₂ + η = (ENNReal.ofReal t)⁻¹ • μ :=
    normalized_vertices hI hJ hdis hmI hmJ
  have hbalance : occupation ρ = c • graphDemand μ E := by
    rw [hfeas.2.2.2, hvertices, graphDemand, Measure.prod_smul_left, Measure.prod_smul_right,
      Measure.restrict_smul, Measure.restrict_smul, smul_smul]
    rfl
  have hc : c ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr htpos).ne')
      (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr htpos).ne')
  have hdemandAC : c • graphDemand μ E ≪ μ.prod μ :=
    Measure.absolutelyContinuous_restrict.smul_left c
  have hlicensed (n : ℕ) : ∀ᵐ v ∂ρ n, charge Y v ≤ 1 := by
    have hpairs (i j : Fin n) (hij : i ≠ j) :
        (ρ n).map (fun v => (v i, v j)) ≪ μ.prod μ := by
      apply Measure.AbsolutelyContinuous.trans _ hdemandAC
      apply Measure.absolutelyContinuous_of_le
      rw [← hbalance]
      exact (pair_le_orderOccupation n (ρ n) ⟨(i, j), hij⟩).trans
        (Measure.le_sum (fun n => orderOccupation n (ρ n)) n)
    filter_upwards [hfeas.2.2.1 n,
      ae_charge_le_of_pair_marginals μ hG hY b hb hbound htests (ρ n) hpairs] with v hv ht
    exact ht hv
  have hi (ν : Measure (Ω × Ω)) [IsFiniteMeasure ν] : Integrable Y ν := by
    exact Integrable.of_bound hY.aestronglyMeasurable b
      (Eventually.of_forall (fun p => by simpa only [Real.norm_eq_abs] using hbound p))
  have hD : TwoCenterPhysicalSlack.demand σ₁ σ₂ η E = c • graphDemand μ E :=
    (TwoCenterPhysicalSlack.laws_occupation σ₁ σ₂ η hη E hE hEsym).symm.trans hbalance
  have : IsFiniteMeasure (TwoCenterPhysicalSlack.demand σ₁ σ₂ η E) := by
    unfold TwoCenterPhysicalSlack.demand
    infer_instance
  have hbare := TwoCenterPhysicalSlack.objective_le_bare_slack σ₁ σ₂ η hη E hE hEsym Y
    (hi _) (hi _) (hi _) hlicensed
  have hYedges : (∫ p, Y p ∂graphDemand μ E) = ∫ p, Y p ∂μ.prod μ := by
    rw [graphDemand, ← integral_indicator hE]
    apply integral_congr_ae
    exact Eventually.of_forall (fun p => by
      by_cases hg : G p = true
      · exact indicator_of_mem (show p ∈ E from hg) _
      · have hz := hzero p (Bool.eq_false_iff.mpr hg)
        simp only [indicator_of_notMem (show p ∉ E from hg), hz])
  have hpairMean : TwoCenterPhysicalSlack.headPairMean σ₁ σ₂ Y = ∫ p, Y p ∂σ₁.prod σ₂ := by
    have hs : (∫ p, Y p ∂σ₂.prod σ₁) = ∫ p, Y p ∂σ₁.prod σ₂ := by
      simpa only [hYsym] using (integral_prod_swap (μ := σ₁) (ν := σ₂) Y)
    rw [TwoCenterPhysicalSlack.headPairMean, hs]
    ring
  have hcval : c.toReal = 1 / t ^ 2 := by
    simp only [c, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal htpos.le]
    ring
  rw [hD, integral_smul_measure, hcval, smul_eq_mul, hYedges, hpairMean] at hbare
  have hscaled := mul_le_mul_of_nonneg_left hbare (sq_nonneg t)
  have hid : t ^ 2 * (1 / t ^ 2 * (∫ p, Y p ∂μ.prod μ) / 2) = (∫ p, Y p ∂μ.prod μ) / 2 := by
    field_simp
  rw [hid] at hscaled
  have hT : (∫ p, Y p ∂σ₁.prod σ₂) ≤ 1 := by
    simpa only [integral_const, probReal_univ, smul_eq_mul, mul_one] using
      integral_mono_ae (hi (σ₁.prod σ₂)) (integrable_const (1 : ℝ)) (Eventually.of_forall hupper)
  have hp0 := mul_le_mul_of_nonneg_left (TwoCenterPhysicalSlack.bareProbability_lower_bound η E) (sq_nonneg t)
  have hcoefficient : t ^ 2 * (1 - η.real univ) = t * (3 * t - 1) := by
    rw [normalizedRemainder_mass hI hJ hdis htpos hmI hmJ]
    field_simp
    ring
  rw [hcoefficient] at hp0
  have himprove := mul_le_mul_of_nonneg_right hp0 (sub_nonneg.mpr hT)
  nlinarith


omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
/-- The actual conditional head price never exceeds the original color's
unit upper charge bound, without any optimality assumption. -/
theorem headPrice_le_one (W : CappedModel.Model Ω μ) (I J : Set Ω)
    (hI : μ I ≠ 0) (hJ : μ J ≠ 0) : headPrice W I J ≤ 1 := by
  have : IsProbabilityMeasure (headLaw μ I) := cellLaw_probability μ I hI
  have : IsProbabilityMeasure (headLaw μ J) := cellLaw_probability μ J hJ
  have hac := (cellLaw_absolutelyContinuous μ I).prod (cellLaw_absolutelyContinuous μ J)
  have hmeas : StronglyMeasurable (fun p : Ω × Ω => CappedModel.chargeKernel W p.1 p.2) :=
    W.stronglyMeasurable_moment CappedColor.continuous_charge.measurable.stronglyMeasurable
  have hi : Integrable (fun p : Ω × Ω => CappedModel.chargeKernel W p.1 p.2)
      ((headLaw μ I).prod (headLaw μ J)) :=
    Integrable.of_bound hmeas.aestronglyMeasurable 3 (hac.ae_le (CappedModel.chargeKernel_bound W))
  have hu : ∀ᵐ p ∂(headLaw μ I).prod (headLaw μ J), CappedModel.chargeKernel W p.1 p.2 ≤ 1 :=
    Eventually.of_forall (fun p => (CappedModel.charge_moment_le_adjacency W p).trans
      (CappedModel.adjacency_moment_mem W p).2)
  simpa only [headPrice, integral_const, probReal_univ, smul_eq_mul, mul_one] using
    integral_mono_ae hi (integrable_const (1 : ℝ)) hu

section Multipartite

variable {ι : Type*} [Countable ι]

local instance headPriceOptionMeasurable : MeasurableSpace (Option ι) := ⊤

/-- Actual complete multipartite support, retaining genuine clique dust. -/
def partitionAdj (q : Ω → Option ι) (p : Ω × Ω) : Bool :=
  decide (q p.1 ≠ q p.2 ∨ q p.1 = none)

omit [StandardBorelSpace Ω] [MeasurableEq Ω] in
theorem measurable_partitionAdj (q : Ω → Option ι) (hq : Measurable q) : Measurable (partitionAdj q) :=
  (measurable_of_countable (fun p : Option ι × Option ι => decide (p.1 ≠ p.2 ∨ p.1 = none))).comp
    ((hq.comp measurable_fst).prodMk (hq.comp measurable_snd))

omit [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω] [Countable ι] in
theorem partitionAdj_symm (q : Ω → Option ι) (x y : Ω) : partitionAdj q (x, y) = partitionAdj q (y, x) := by
  by_cases he : q x = q y
  · simp only [partitionAdj, he, ne_eq, not_true_eq_false, false_or]
  · simp only [partitionAdj, he, Ne.symm he, ne_eq, not_false_eq_true, true_or, decide_true]

omit [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω] [Countable ι] in
/-- Every actual independent head is joined exactly to its own complement. -/
theorem partitionAdj_head_row (q : Ω → Option ι) (i : ι) (p : Ω × Ω)
    (hi : p.1 ∈ q ⁻¹' {some i}) :
    partitionAdj q p = true ↔ p.2 ∉ q ⁻¹' {some i} := by
  change q p.1 = some i at hi
  change decide (q p.1 ≠ q p.2 ∨ q p.1 = none) = true ↔ q p.2 ≠ some i
  rw [hi]
  simp only [Option.some_ne_none, or_false, decide_eq_true_eq]
  exact ne_comm

/-- The actual fully feasible multipartite model pays bare-head slack at
its own current conditional two-head charge mean. Countable other heads
and genuine clique dust need no approximation or independence assumption. -/
theorem objective_le_two_head_price (W : CappedModel.Model Ω μ) (hW : CappedModel.FullFeasible W)
    (q : Ω → Option ι) (hq : Measurable q) (i j : ι) (hij : i ≠ j)
    {t : ℝ} (ht : 1 / 3 < t) (hmI : μ.real (q ⁻¹' {some i}) = t)
    (hmJ : μ.real (q ⁻¹' {some j}) = t)
    (hA : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if q p.1 ≠ q p.2 ∨ q p.1 = none then 1 else 0) :
    CappedModel.objective W ≤ t ^ 2 - t * (3 * t - 1) *
      (1 - headPrice W (q ⁻¹' {some i}) (q ⁻¹' {some j})) := by
  let G := partitionAdj q
  have hG : Measurable G := measurable_partitionAdj q hq
  have hGsym : ∀ x y, G (x, y) = G (y, x) := partitionAdj_symm q
  have hAbool : ∀ᵐ p ∂μ.prod μ,
      W.moment CappedColor.adjacency p = if G p = true then 1 else 0 := by
    simpa only [G, partitionAdj, decide_eq_true_eq] using hA
  obtain ⟨Y, hY, hYsym, hbound, hzero, hYe, htests⟩ :=
    CappedModel.BinaryRepresentative.exists_scalar_representative W hW G hG hGsym hAbool
  have hI := hq (measurableSet_singleton (some i))
  have hJ := hq (measurableSet_singleton (some j))
  have hdis : Disjoint (q ⁻¹' {some i}) (q ⁻¹' {some j}) :=
    disjoint_left.mpr (fun x hx hy => hij (Option.some.inj (hx.symm.trans hy)))
  have hphys : ∀ n, 2 ≤ n → ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ), Clique G v → charge Y v ≤ 1 := by
    intro n _
    filter_upwards [htests n] with v hv hc
    change charge (Function.uncurry (fun x y => Y (x, y))) v ≤ 1
    rw [physicalCharge_eq_tupleCharge]
    exact hv hc
  have hscalar := scalar_objective_le_head_price G hG (fun p => hGsym p.2 p.1) Y hY
    (fun p => hYsym p.2 p.1) 3 (by norm_num)
    (fun p => abs_le.mpr ⟨(hbound p).1, (hbound p).2.trans (by norm_num)⟩)
    (fun p => (hbound p).2) hzero hphys hI hJ hdis ht hmI hmJ
    (Eventually.of_forall (partitionAdj_head_row q i))
    (Eventually.of_forall (partitionAdj_head_row q j))
  have hI0 : μ (q ⁻¹' {some i}) ≠ 0 := by
    intro hz
    rw [measureReal_def, hz, ENNReal.toReal_zero] at hmI
    linarith
  have hJ0 : μ (q ⁻¹' {some j}) ≠ 0 := by
    intro hz
    rw [measureReal_def, hz, ENNReal.toReal_zero] at hmJ
    linarith
  have : IsProbabilityMeasure (headLaw μ (q ⁻¹' {some i})) := cellLaw_probability μ _ hI0
  have : IsProbabilityMeasure (headLaw μ (q ⁻¹' {some j})) := cellLaw_probability μ _ hJ0
  have hhead := ((cellLaw_absolutelyContinuous μ (q ⁻¹' {some i})).prod
    (cellLaw_absolutelyContinuous μ (q ⁻¹' {some j}))).ae_le hYe
  rw [integral_congr_ae hYe, integral_congr_ae hhead] at hscalar
  exact hscalar

end Multipartite

end Erdos1017.MultipartiteHeadPrice
