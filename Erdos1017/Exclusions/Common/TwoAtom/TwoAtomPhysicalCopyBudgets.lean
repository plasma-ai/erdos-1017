module

public import Erdos1017.Exclusions.Common.Covered.FullCoveredCopyVariation
public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomBlockGeometry
public import Erdos1017.Exclusions.Common.TwoAtom.TwoAtomOwnRowBounds

/-!
# Copy-gain budgets of a four-region optimum

The own covered-copy comparison of a four-region optimum gives all three
physical no-positive-gain budgets, with body nonpositivity taken as an explicit
premise on the original charge.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace Erdos1017.CappedModel

private theorem integral_labels {Ω ι : Type*} [MeasurableSpace Ω]
    [MeasurableSpace ι] [Fintype ι] [DiscreteMeasurableSpace ι]
    {μ : Measure Ω} [IsFiniteMeasure μ] (q : Ω → ι) (hq : Measurable q) (f : ι → ℝ) :
    (∫ z, f (q z) ∂μ) = ∑ i, μ.real (q ⁻¹' {i}) * f i := by
  have he : (fun z => f (q z)) =
      fun z => ∑ i, (q ⁻¹' {i}).indicator (fun _ => f i) z := by
    funext z
    simp [Set.indicator_apply]
  rw [he, integral_finsetSum Finset.univ (fun i _ =>
    (integrable_const (f i)).indicator (hq (measurableSet_singleton i)))]
  simp_rw [integral_indicator (hq (measurableSet_singleton _)), setIntegral_const,
    smul_eq_mul]

private theorem block_property_of_ae {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (q : Ω → ι)
    (hpositive : ∀ i, 0 < μ (q ⁻¹' {i})) (P : ι → ι → Prop)
    (hP : ∀ᵐ p ∂μ.prod μ, P (q p.1) (q p.2)) : ∀ i j, P i j := by
  intro i j
  obtain ⟨x, hx, hpx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (hpositive i).ne' (ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hP))
  obtain ⟨z, hz, hpz⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (hpositive j).ne' (ae_restrict_of_ae hpx)
  exact hx ▸ hz ▸ hpz

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- The actual four-region optimum's own covered-copy comparison gives
all three physical no-positive-gain budgets. Body nonpositivity is an
explicit original-charge premise; it is not inferred from signed count
feasibility. No selected structure or supplied row/budget certificate is used. -/
theorem FullStationaryClass.twoAtom_copy_gain_budgets
    {d c m : ℝ} {W : Model Ω μ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (q : Ω → Fin 4) (hq : Measurable q) (hpositive : ∀ i, 0 < μ (q ⁻¹' {i}))
    (x : TwoAtomCountGate.Coefficients) (hx : x ∈ TwoAtomCountGate.feasible)
    (hmom : ∀ p : Ω × Ω,
      W.moment CappedColor.adjacency p =
        (if TwoAtomCountGate.blockAdjacency (q p.1) (q p.2) = true then 1 else 0) ∧
      W.moment CappedColor.charge p = TwoAtomCountGate.blockCharge x (q p.1) (q p.2))
    (hbody : ∀ᵐ p ∂μ.prod μ,
      q p.1 ≠ 1 → q p.2 ≠ 1 → chargeKernel W p.1 p.2 ≤ 0) :
    TwoAtomCountGate.CopyGainBudgets x (μ.real (q ⁻¹' {0})) (μ.real (q ⁻¹' {1}))
      (-m) (2 * (c - m * d) + m) := by
  let G := TwoAtomCountGate.blockAdjacency
  let C := TwoAtomCountGate.blockCharge x
  let A := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  let I := q ⁻¹' {1}
  let mass (i : Fin 4) := μ.real (q ⁻¹' {i})
  let ν := 2 * (c - m * d)
  let gamma := ν + m
  let rY (i j k : Fin 4) : ℝ :=
    if (G i k && G j k) = true then C i k + C j k + C i j * (if k = 1 then 1 else 0)
    else 0
  let rA (i j k : Fin 4) : ℝ := if (G i k && G j k) = true then 1 else 0
  have hI : MeasurableSet I := hq (measurableSet_singleton 1)
  have hind : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → p.2 ∈ I →
      adjacencyKernel W p.1 p.2 = 0 := by
    exact Eventually.of_forall (fun p hi hj => by
      change q p.1 = 1 at hi
      change q p.2 = 1 at hj
      change W.moment CappedColor.adjacency p = 0
      simp [hmom p, hi, hj, TwoAtomCountGate.blockAdjacency])
  have hcopy := hW.ae_covered_copy_shifted_row_le_stationary hd hgap I hI hind hbody
  have hs := (hW.strict_gap_structure hd hgap).strict_support
  have hrep : ∀ᵐ p ∂μ.prod μ,
      A p.1 p.2 = G (q p.1) (q p.2) ∧ Y p.1 p.2 = C (q p.1) (q p.2) := by
    filter_upwards [PhysicalRepresentative.adjacency_moment_ae_eq W m hs,
      PhysicalRepresentative.charge_ae_eq W m hs] with p ha hy
    have he := ha.symm.trans (hmom p).1
    change (if A p.1 p.2 = true then (1 : ℝ) else 0) =
      (if G (q p.1) (q p.2) = true then 1 else 0) at he
    constructor
    · cases hA : A p.1 p.2 <;> cases hG : G (q p.1) (q p.2) <;> simp_all
    · exact hy.trans (hmom p).2
  have hsections := Measure.ae_ae_of_ae_prod hrep
  have hpair : ∀ᵐ p ∂μ.prod μ,
      q p.1 ≠ 1 → q p.2 ≠ 1 → G (q p.1) (q p.2) = true →
      (∑ k, mass k * rY (q p.1) (q p.2) k) -
        m * (∑ k, mass k * rA (q p.1) (q p.2) k) ≤ ν := by
    filter_upwards [hcopy, hrep, Measure.quasiMeasurePreserving_fst.ae hsections,
      Measure.quasiMeasurePreserving_snd.ae hsections] with p hp he hx hy hpx hpy hG
    have h := hp hpx hpy (he.1.trans hG)
    have hrowY : IndependentAtomCopy.rowCharge A Y I p.1 p.2 =ᵐ[μ]
        fun z => rY (q p.1) (q p.2) (q z) := by
      filter_upwards [hx, hy] with z hx hy
      change (if (A p.1 z && A p.2 z) = true then
        Y p.1 z + Y p.2 z + Y p.1 p.2 * I.indicator (fun _ => 1) z else 0) = _
      rw [hx.1, hy.1, hx.2, hy.2, he.2]
      by_cases hz : q z = 1 <;> simp [rY, I, hz]
    have hrowA : IndependentAtomCopy.rowAdjacency A p.1 p.2 =ᵐ[μ]
        fun z => rA (q p.1) (q p.2) (q z) := by
      filter_upwards [hx, hy] with z hx hy
      change (if (A p.1 z && A p.2 z) = true then (1 : ℝ) else 0) = _
      rw [hx.1, hy.1]
    change (∫ z, IndependentAtomCopy.rowCharge A Y I p.1 p.2 z ∂μ) -
      m * (∫ z, IndependentAtomCopy.rowAdjacency A p.1 p.2 z ∂μ) ≤ ν at h
    rw [integral_congr_ae hrowY, integral_congr_ae hrowA,
      integral_labels q hq (rY (q p.1) (q p.2)),
      integral_labels q hq (rA (q p.1) (q p.2))] at h
    exact h
  have hblocks := block_property_of_ae q hpositive
    (fun i j => i ≠ 1 → j ≠ 1 → G i j = true →
      (∑ k, mass k * rY i j k) - m * (∑ k, mass k * rA i j k) ≤ ν) hpair
  have hRR := hblocks 2 2 (by decide) (by decide) (by decide)
  have hEE := hblocks 3 3 (by decide) (by decide) (by decide)
  have hRE := hblocks 2 3 (by decide) (by decide) (by decide)
  have hown (i : Fin 4) :
      (∑ k, mass k * (C i k - m * (if G i k = true then 1 else 0))) = ν := by
    obtain ⟨z, hz, hstat⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (hpositive i).ne' (ae_restrict_of_ae hW.stationary)
    have hqz : q z = i := hz
    have heq : (∫ w, shiftedKernel W m z w ∂μ) =
        ∫ w, C i (q w) - m * (if G i (q w) = true then 1 else 0) ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun w => by
        rw [shiftedKernel, shiftedMoment_eq, (hmom (z, w)).1, (hmom (z, w)).2, hqz])
    rw [heq, integral_labels q hq (fun k => C i k - m * (if G i k = true then 1 else 0))]
      at hstat
    exact hstat
  have hR := hown 2
  have hE := hown 3
  have hmass : mass 0 + mass 1 + mass 2 + mass 3 = 1 := by
    have h := integral_labels (μ := μ) q hq (fun _ => (1 : ℝ))
    simpa [Fin.sum_univ_succ, mass, add_assoc] using h.symm
  have hMmass := congrArg (fun v : ℝ => m * v) hmass
  simp [rY, rA, G, C, TwoAtomCountGate.blockAdjacency, TwoAtomCountGate.blockCharge,
    Fin.sum_univ_succ] at hRR hEE hRE hR hE
  have hLRR : gamma - mass 1 * x 2 ≤ 0 := by
    dsimp only [gamma]
    nlinarith only [hRR, hR, hMmass]
  have hLEE : gamma - m * mass 0 - mass 1 * x 3 ≤ 0 := by
    dsimp only [gamma]
    nlinarith only [hEE, hE, hMmass]
  have hLRE : gamma + x 0 * mass 0 - mass 1 * x 4 ≤ 0 := by
    dsimp only [gamma]
    nlinarith only [hRE, hR, hE, hMmass]
  constructor
  · refine ⟨1, by norm_num, ?_⟩
    intro s hs _
    have hl := mul_nonpos_of_nonneg_of_nonpos hs.le hLRR
    have hq := mul_nonneg hx.1 (sq_nonneg s)
    change s * (gamma - mass 1 * x 2) - x 2 * s ^ 2 / 2 ≤ 0
    nlinarith only [hl, hq]
  · refine ⟨1, by norm_num, ?_⟩
    intro s hs _
    have hl := mul_nonpos_of_nonneg_of_nonpos hs.le hLEE
    have hq := mul_nonneg hx.2.1 (sq_nonneg s)
    change s * (gamma + -m * mass 0 - mass 1 * x 3) - x 3 * s ^ 2 / 2 ≤ 0
    nlinarith only [hl, hq]
  · refine ⟨1, by norm_num, ?_⟩
    intro s hs _
    have hl := mul_nonpos_of_nonneg_of_nonpos hs.le hLRE
    have hq := mul_nonneg hx.1 (sq_nonneg s)
    change s * (gamma + x 0 * mass 0 - mass 1 * x 4) - x 2 * s ^ 2 / 2 ≤ 0
    nlinarith only [hl, hq]

end Erdos1017.CappedModel
