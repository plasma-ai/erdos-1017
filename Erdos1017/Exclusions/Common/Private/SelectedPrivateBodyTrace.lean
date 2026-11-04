module

public import Erdos1017.Exclusions.Common.Physical.ModelIndependentCoverInsertion
public import Erdos1017.Exclusions.Common.Private.SelectedPrivateCopyCubic
public import Erdos1017.Exclusions.Common.Physical.PhysicalPositiveCover

/-!
# Strict trace inequality for a private head

A private head and its distinct whole outside hole cannot form a positive-charge
cover, so the body energy is positive and the private-head trace inequality is
strict, including the zero-body case, retaining the partner square and the
missing partner-to-body cross terms.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

attribute [local instance] Classical.propDecidable

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem degree_on_independent_joined_cover (H : Set Ω) (hH : MeasurableSet H)
    (hind : ∀ᵐ p ∂μ.prod μ, p.1 ∈ H → p.2 ∈ H → adjacencyKernel W p.1 p.2 = 0)
    (hjoin : ∀ᵐ p ∂μ.prod μ, p.1 ∈ H → p.2 ∉ H → adjacencyKernel W p.1 p.2 = 1) :
    ∀ᵐ x ∂μ, x ∈ H →
      adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x = 1 - μ.real H := by
  filter_upwards [Measure.ae_ae_of_ae_prod hind, Measure.ae_ae_of_ae_prod hjoin,
    KernelOperator.onL2_coe (adjacencyKernel W) (adjacencyKernel_measurable W)
      (adjacencyKernel_bound W) (Lp.const 2 μ (1 : ℝ))] with x hi hj hop hmem
  change KernelOperator.onL2 (adjacencyKernel W) (adjacencyKernel_measurable W)
    (adjacencyKernel_bound W) (Lp.const 2 μ (1 : ℝ)) x = _
  rw [hop, KernelOperator.applyKernel]
  have he : (fun y => adjacencyKernel W x y * Lp.const 2 μ (1 : ℝ) y) =ᵐ[μ]
      fun y => 1 - H.indicator (fun _ => (1 : ℝ)) y := by
    filter_upwards [hi, hj, Lp.coeFn_const 2 μ (1 : ℝ)] with y hi hj hone
    rw [hone]
    by_cases hyH : y ∈ H
    · simp only [hi hmem hyH, zero_mul, indicator_of_mem hyH, sub_self]
    · simp only [hj hmem hyH, one_mul, indicator_of_notMem hyH, sub_zero, Function.const_apply]
  rw [integral_congr_ae he,
    integral_sub (integrable_const 1) ((integrable_const 1).indicator hH),
    integral_const, integral_indicator hH, setIntegral_const]
  simp only [probReal_univ, smul_eq_mul, mul_one]

/-- A private original head and its distinct whole outside hole cannot
form a positive-charge cover. The actual crossing completion and original
degree separation exclude zero positive-body energy. -/
theorem private_body_energy_pos (S : SelectedHighLowStructure W m) (r u : S.I)
    (hru : r ≠ u) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hprivate : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val →
      adjacencyKernel W p.1 p.2 = if S.ρ p.2 = r.val ∨ S.ρ p.2 = u.val then 0 else 1) :
    0 < ∫ p : Ω × Ω,
      (IndependentAtomCopy.positiveBody (PhysicalRepresentative.charge W m)
        ({x | S.ρ x = r.val} ∪ {x | S.ρ x = u.val}) p.1 p.2) ^ 2 ∂μ.prod μ := by
  let I := {x | S.ρ x = r.val}
  let P := {x | S.ρ x = u.val}
  let H := I ∪ P
  let Y := PhysicalRepresentative.charge W m
  let K := IndependentAtomCopy.positiveBody Y H
  have hI : MeasurableSet I := (S.hfibers r.val r.property).1
  have hP : MeasurableSet P := (S.hfibers u.val u.property).1
  have hH : MeasurableSet H := hI.union hP
  have hzero : ∀ᵐ p ∂μ.prod μ, p.1 ∈ P → p.2 ∈ P →
      adjacencyKernel W p.1 p.2 = 0 := by
    have h := (S.hfibers u.val u.property).2.2.1
    rw [Measure.prod_restrict] at h
    exact ((ae_restrict_iff' (hP.prod hP)).mp h).mono (fun _ hp hx hy => hp ⟨hx, hy⟩)
  have hreverse := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    hprivate
  have hind : ∀ᵐ p ∂μ.prod μ, p.1 ∈ H → p.2 ∈ H →
      adjacencyKernel W p.1 p.2 = 0 := by
    filter_upwards [hprivate, hreverse, hzero, adjacencyKernel_symm W]
      with p hi hr hp hs hx hy
    rcases hx with hx | hx
    · exact (hi hx).trans (ite_eq_left hy)
    · rcases hy with hy | hy
      · exact hs.trans ((hr hy).trans (ite_eq_left (Or.inr hx)))
      · exact hp hx hy
  have hnonneg : 0 ≤ ∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ :=
    integral_nonneg (fun _ => sq_nonneg _)
  by_contra hnot
  have henergy : (∫ p : Ω × Ω, (K p.1 p.2) ^ 2 ∂μ.prod μ) = 0 :=
    le_antisymm (le_of_not_gt hnot) hnonneg
  have hbody : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry Y) H = 0 := by
    rw [PhysicalPrimal.bodyPositiveEnergy, ← integral_indicator (hH.compl.prod hH.compl)]
    convert henergy using 1
    apply integral_congr_ae
    exact Eventually.of_forall (fun p => by
      by_cases hx : p.1 ∈ H <;> by_cases hy : p.2 ∈ H <;>
        simp [K, IndependentAtomCopy.positiveBody, Function.uncurry, hx, hy])
  have hcoverY := PhysicalPrimal.ae_nonpositive_of_bodyPositiveEnergy_zero μ
    (Function.uncurry Y) (PhysicalRepresentative.measurable_charge W m) 3
    (fun p => PhysicalRepresentative.charge_bound W m p.1 p.2) H hH hbody
  have hs := (hW.strict_gap_structure hd hgap).strict_support
  have hcover : ∀ᵐ p ∂μ.prod μ, p.1 ∉ H → p.2 ∉ H →
      chargeKernel W p.1 p.2 ≤ 0 := by
    filter_upwards [hcoverY, PhysicalRepresentative.charge_ae_eq W m hs] with p hp he hx hy
    rw [← he]
    exact hp hx hy
  have hjoin := hW.no_missing_cross_on_independent_positive_cover hd.2 hgap H hH hind hcover
  have hdegree := degree_on_independent_joined_cover H hH hind hjoin
  have hgood : ∀ᵐ p ∂(μ.restrict I).prod (μ.restrict P), False := by
    filter_upwards [ae_mono (Measure.prod_mono Measure.restrict_le_self
        Measure.restrict_le_self) hind,
      ae_mono (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self) hW.moment_mem,
      ae_mono (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self) hs,
      ae_mono (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self) S.hdegreeNe,
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_of_ae hdegree),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_of_ae hdegree),
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hI),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hP)] with p hi hm hs hn hd₁ hd₂ hx hy
    have hG : adjacencyKernel W p.1 p.2 = 0 := hi (Or.inl hx) (Or.inr hy)
    have hM : shiftedKernel W m p.1 p.2 = 0 := by
      change adjacencyKernel W p.1 p.2 =
        if 0 < shiftedKernel W m p.1 p.2 then 1 else 0 at hs
      have hnpos : ¬0 < shiftedKernel W m p.1 p.2 := by
        intro hpos
        rw [ite_eq_left hpos] at hs
        linarith
      exact le_antisymm (le_of_not_gt hnpos) hm.1
    have hne : S.ρ p.1 ≠ S.ρ p.2 := fun h => hru (Subtype.ext (hx.symm.trans (h.trans hy)))
    exact (hn ⟨hM, hne⟩) ((hd₁ (Or.inl hx)).trans (hd₂ (Or.inr hy)).symm)
  obtain ⟨x, _, hx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers r.val r.property).2.1.ne' (Measure.ae_ae_of_ae_prod hgood)
  obtain ⟨y, _, hy⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers u.val u.property).2.1.ne' hx
  exact hy

/-- The exact private inventory retains the partner square and every
missing partner-to-body cross contribution. Body positivity is derived
from the original independent-cover obstruction. -/
theorem private_body_strong_trace (S : SelectedHighLowStructure W m) (r u : S.I)
    (hru : r ≠ u) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hprivate : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val →
      adjacencyKernel W p.1 p.2 = if S.ρ p.2 = r.val ∨ S.ρ p.2 = u.val then 0 else 1)
    (hb : μ.real {x | S.ρ x = u.val} ≤ 2 * (c - m * d) + m) :
    let A := μ.real {x | S.ρ x = r.val}
    let b := μ.real {x | S.ρ x = u.val}
    let gamma := 2 * (c - m * d) + m
    let U := ({x | S.ρ x = r.val} ∪ {x | S.ρ x = u.val})ᶜ \ S.rootNeighborhood u
    2 * (A + b) ^ 2 + (A + gamma - b) ^ 2 + 4 * b * μ.real U ≤ 2 * (1 - 2 * d) := by
  have htrace := S.private_positive_body_trace r u hru hW hd hgap hprivate hb
    (S.private_body_energy_pos r u hru hW hd hgap hprivate)
  have hinventory := S.private_body_missing_inventory r u hru hW hd hgap hprivate
  dsimp only at htrace hinventory ⊢
  nlinarith only [htrace, hinventory]

/-- The actual private-head trace is strict, including the zero-body
case. Positive energy, the private inventory and the original copy bound
are all derived internally from the same selected model. -/
theorem private_body_strict_trace (S : SelectedHighLowStructure W m) (r u : S.I)
    (hru : r ≠ u) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hprivate : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val →
      adjacencyKernel W p.1 p.2 = if S.ρ p.2 = r.val ∨ S.ρ p.2 = u.val then 0 else 1)
    (hb : μ.real {x | S.ρ x = u.val} ≤ 2 * (c - m * d) + m)
    (hgamma : 2 * (c - m * d) + m < μ.real {x | S.ρ x = r.val}) :
    3 * (μ.real {x | S.ρ x = r.val}) ^ 2 +
      2 * μ.real {x | S.ρ x = r.val} * (2 * (c - m * d) + m) +
      (2 * (c - m * d) + m) ^ 2 < 2 * (1 - 2 * d) := by
  exact S.private_positive_body_strict_trace r u hru hW hd hgap hprivate hb hgamma
    (S.private_body_energy_pos r u hru hW hd hgap hprivate)

end Erdos1017.CappedModel.SelectedHighLowStructure
