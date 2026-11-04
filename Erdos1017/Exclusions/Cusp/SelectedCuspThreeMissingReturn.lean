module

public import Erdos1017.Exclusions.Cusp.SelectedCuspThreeLowSlopeGeometry
public import Erdos1017.Exclusions.Common.Saturation.SelectedUnsaturatedAtomDegree
public import Erdos1017.Exclusions.Common.TwoCenter.OneCenterSourceCredit
public import Erdos1017.SelectedModel.Flows.IntegrableDensityReturn

/-!
# Density return of the third-cusp missing region

The entire missing region has a positive original degree slope, so its negative
reweighting cannot return to the original density, endpoint included
(`cusp_three_missing_return`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

open KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m d c : ℝ}

private theorem missing_direction_data (S : SelectedHighLowStructure W m) (i : S.I)
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) :
    let I := {x | S.ρ x = i.val}
    let J := S.cuspThreeMissingRegion i
    let N := S.rootNeighborhood i
    let f := MissingFlow.OneCenter.sourceDirection μ I J
    (∫ x, f x ∂μ) = 0 ∧
      (∫ x, adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x * f x ∂μ) =
        μ.real J * μ.real N - ∫ x in J, adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x ∂μ ∧
      (∫ x, adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x * f x ∂μ) =
        (∫ p in J ×ˢ N, 1 - adjacencyKernel W p.1 p.2 ∂μ.prod μ) -
          ∫ p in J ×ˢ J, adjacencyKernel W p.1 p.2 ∂μ.prod μ ∧
      kernelEnergy (μ := μ) (adjacencyKernel W) f =
        ∫ p in J ×ˢ J, adjacencyKernel W p.1 p.2 ∂μ.prod μ ∧
      kernelEnergy (μ := μ) (shiftedKernel W m) f =
        ∫ p in J ×ˢ J, shiftedKernel W m p.1 p.2 ∂μ.prod μ := by
  let I := {x | S.ρ x = i.val}
  let J := S.cuspThreeMissingRegion i
  let N := S.rootNeighborhood i
  let f := MissingFlow.OneCenter.sourceDirection μ I J
  let g := adjacencyOperator W (Lp.const 2 μ (1 : ℝ))
  have hI : MeasurableSet I := (S.hfibers i.val i.property).1
  have hJ : MeasurableSet J := S.measurableSet_cuspThreeMissingRegion i
  have hN : MeasurableSet N := S.measurableSet_rootNeighborhood i
  have hA : 0 < μ.real I :=
    ENNReal.toReal_pos (S.hfibers i.val i.property).2.1.ne' (measure_ne_top μ _)
  have hdisIJ : Disjoint I J := disjoint_left.mpr (fun _ hx hy => hy.1 hx)
  have hdisIN : Disjoint I N := S.rootNeighborhood_disjoint i
  have hdisJN : Disjoint J N := disjoint_left.mpr (fun _ hx hy => hx.2 hy)
  have hpartition (x : Ω) : x ∈ I ∨ x ∈ J ∨ x ∈ N := by
    by_cases hxI : x ∈ I
    · exact Or.inl hxI
    · by_cases hxN : x ∈ N
      · exact Or.inr (Or.inr hxN)
      · exact Or.inr (Or.inl ⟨hxI, hxN⟩)
  have hGzero : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → p.2 ∈ I ∪ J →
      adjacencyKernel W p.1 p.2 = 0 := by
    filter_upwards [S.ae_original_root_adjacency i hW hd hgap] with p hp hx hy
    rw [hp hx]
    have hn : p.2 ∉ N := hy.elim
      (fun h => disjoint_left.mp hdisIN h) (fun h => h.2)
    exact ite_eq_right hn
  have hGII := hGzero.mono (fun _ hp hx hy => hp hx (Or.inl hy))
  have hGIJ := hGzero.mono (fun _ hp hx hy => hp hx (Or.inr hy))
  have hGJI : ∀ᵐ p ∂μ.prod μ, p.1 ∈ J → p.2 ∈ I →
      adjacencyKernel W p.1 p.2 = 0 := by
    filter_upwards [adjacencyKernel_symm W,
      Measure.measurePreserving_swap.quasiMeasurePreserving.ae hGIJ] with p hs hp hx hy
    exact hs.trans (hp hy hx)
  have hMzero : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → p.2 ∈ I ∪ J →
      shiftedKernel W m p.1 p.2 = 0 := by
    filter_upwards [hW.complementary, hGzero] with p hc hz hx hy
    change (1 - adjacencyKernel W p.1 p.2) * shiftedKernel W m p.1 p.2 = 0 at hc
    simpa only [hz hx hy, sub_zero, one_mul] using hc
  have hMII := hMzero.mono (fun _ hp hx hy => hp hx (Or.inl hy))
  have hMIJ := hMzero.mono (fun _ hp hx hy => hp hx (Or.inr hy))
  have hmean : (∫ x, f x ∂μ) = 0 := by
    dsimp [f, MissingFlow.OneCenter.sourceDirection]
    rw [integral_sub ((MissingFlow.OneCenter.integrable_recipientDensity hI).const_mul _)
      ((integrable_const 1).indicator hJ), integral_const_mul,
      MissingFlow.OneCenter.integral_recipientDensity hI hA, integral_indicator hJ,
      setIntegral_const, smul_eq_mul]
    ring
  have hg : Integrable (g : Ω → ℝ) μ := (Lp.memLp g).integrable (by norm_num)
  have hgi : (∫ x in I, g x ∂μ) = μ.real I * μ.real N := by
    have he := wholeRowFiber_degree W m S.ρ i.val (S.hfibers i.val i.property).2.2.2
    rw [S.wholeRowDegree_eq_neighborhood_mass i] at he
    rw [integral_congr_ae he, setIntegral_const, smul_eq_mul]
  have hdegree : (∫ x, g x * f x ∂μ) =
      μ.real J * μ.real N - ∫ x in J, g x ∂μ := by
    have he : (fun x => g x * f x) = fun x =>
        μ.real J / μ.real I * I.indicator g x - J.indicator g x := by
      funext x
      by_cases hxI : x ∈ I <;> by_cases hxJ : x ∈ J <;>
        simp [f, MissingFlow.OneCenter.sourceDirection,
          MissingFlow.AtomicAssignment.recipientDensity, hxI, hxJ, div_eq_mul_inv] <;> ring
    rw [he, integral_sub ((hg.indicator hI).const_mul _) (hg.indicator hJ),
      integral_const_mul, integral_indicator hI, integral_indicator hJ, hgi]
    field_simp
  have hG : Integrable (fun p : Ω × Ω => adjacencyKernel W p.1 p.2) (μ.prod μ) := by
    simpa only [mul_one] using integrable_kernel_bilinear (adjacencyKernel_measurable W)
      (adjacencyKernel_bound W) (integrable_const (1 : ℝ)) (integrable_const (1 : ℝ))
  have hprod := ((integrable_const (1 : ℝ) (μ := μ)).indicator hJ).mul_prod
    ((integrable_const (1 : ℝ) (μ := μ)).indicator hN)
  have hGj := integrable_kernel_bilinear (adjacencyKernel_measurable W)
    (adjacencyKernel_bound W) (integrable_const (1 : ℝ)) ((integrable_const 1).indicator hJ)
  have hGJJ := hG.indicator (hJ.prod hJ)
  have hinventory : (∫ p in J ×ˢ N, 1 - adjacencyKernel W p.1 p.2 ∂μ.prod μ) =
      μ.real J * μ.real N - (∫ x in J, g x ∂μ) +
        ∫ p in J ×ˢ J, adjacencyKernel W p.1 p.2 ∂μ.prod μ := by
    rw [← integral_indicator (hJ.prod hN)]
    have he : (fun p : Ω × Ω => (J ×ˢ N).indicator
        (fun p => 1 - adjacencyKernel W p.1 p.2) p) =ᵐ[μ.prod μ]
        fun p => J.indicator (fun _ => (1 : ℝ)) p.1 * N.indicator (fun _ => (1 : ℝ)) p.2 -
          adjacencyKernel W p.1 p.2 * 1 * J.indicator (fun _ => (1 : ℝ)) p.1 +
          (J ×ˢ J).indicator (fun p => adjacencyKernel W p.1 p.2) p := by
      filter_upwards [hGJI] with p hz
      by_cases hx : p.1 ∈ J
      · rcases hpartition p.2 with hy | hy | hy
        · have hnJ : p.2 ∉ J := disjoint_left.mp hdisIJ hy
          have hnN : p.2 ∉ N := disjoint_left.mp hdisIN hy
          simp [hx, hnJ, hnN, hz hx hy]
        · have hnN : p.2 ∉ N := disjoint_left.mp hdisJN hy
          simp [hx, hy, hnN]
        · have hnJ : p.2 ∉ J := disjoint_right.mp hdisJN hy
          simp [hx, hy, hnJ]
      · simp [hx]
    rw [integral_congr_ae he]
    have hadd := integral_add (hprod.sub hGj) hGJJ
    simp only [Pi.sub_apply] at hadd
    rw [hadd, integral_sub hprod hGj, integral_prod_mul, integral_indicator hJ, integral_indicator hN,
      setIntegral_const, setIntegral_const, integral_indicator (hJ.prod hJ)]
    have hgj := adjacency_kernelPairing_one_eq_degree W (J.indicator (fun _ => 1))
      ((integrable_const 1).indicator hJ)
    rw [kernelPairing] at hgj
    have hright : (∫ x, adjacencyOperator W (Lp.const 2 μ (1 : ℝ)) x *
        J.indicator (fun _ => 1) x ∂μ) = ∫ x in J, g x ∂μ := by
      rw [← integral_indicator hJ]
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by by_cases hx : x ∈ J <;> simp [hx, g])
    rw [hright] at hgj
    simp only [smul_eq_mul, mul_one] at hgj ⊢
    rw [hgj]
  have hGenergy := MissingFlow.OneCenter.energy_sourceDirection _
    (adjacencyKernel_measurable W) (adjacencyKernel_bound W) (adjacencyKernel_symm W) hI hJ hGII hGIJ
  have hMenergy := MissingFlow.OneCenter.energy_sourceDirection _
    (shiftedKernel_measurable W m) (shiftedKernel_bound W m)
    ((shiftedMoment_symm W m).mono (fun _ hp => hp.symm)) hI hJ hMII hMIJ
  exact ⟨hmean, hdegree, by linarith only [hdegree, hinventory], hGenergy, hMenergy⟩

/-- The actual entire missing region has a positive original degree slope.
Its negative reweighting cannot return to the old density, including the
endpoint where the original peak vanishes. All energies remain unhalved. -/
theorem cusp_three_missing_return (S : SelectedHighLowStructure W m) (i : S.I)
    (hdk : d = 4 / 9) (hW : FullStationaryClass d c W m) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hell : -m < 1) (hpeak : S.IsCommonForwardPeak d c i)
    (hnonuniv : ¬(∀ᵐ p ∂μ.prod μ, S.ρ p.1 = i.val →
      adjacencyKernel W p.1 p.2 = if S.ρ p.2 = i.val then 0 else 1)) :
    let J := S.cuspThreeMissingRegion i
    let A := S.originalAtomMass i
    let t := μ.real J
    let z := (∫ p in J ×ˢ J, adjacencyKernel W p.1 p.2 ∂μ.prod μ) / 2
    let v := ∫ p in J ×ˢ S.rootNeighborhood i, 1 - adjacencyKernel W p.1 p.2 ∂μ.prod μ
    let FJ := ∫ p in J ×ˢ J, shiftedKernel W m p.1 p.2 ∂μ.prod μ
    0 ≤ z ∧ 0 ≤ FJ ∧ 0 < v - 2 * z ∧
      (0 < z → 0 < FJ ∧ (2 + A / t) * z < v) ∧
      (z = 0 → FJ = 0 ∧ 0 < v) ∧ FJ ≤ 2 * (1 - m) * z := by
  let I := {x | S.ρ x = i.val}
  let J := S.cuspThreeMissingRegion i
  let N := S.rootNeighborhood i
  let A := S.originalAtomMass i
  let t := μ.real J
  let z := (∫ p in J ×ˢ J, adjacencyKernel W p.1 p.2 ∂μ.prod μ) / 2
  let v := ∫ p in J ×ˢ N, 1 - adjacencyKernel W p.1 p.2 ∂μ.prod μ
  let FJ := ∫ p in J ×ˢ J, shiftedKernel W m p.1 p.2 ∂μ.prod μ
  let f := MissingFlow.OneCenter.sourceDirection μ I J
  let g := adjacencyOperator W (Lp.const 2 μ (1 : ℝ))
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by norm_num [hdk]
  obtain ⟨ht, hlow, _, _, _⟩ :=
    S.cusp_three_low_slope_missing_region i hdk hW hgap hglobal hell hpeak hnonuniv
  change 0 < t at ht
  change ∀ᵐ x ∂μ.restrict J, x ∈ S.L ∧ g x < wholeRowDegree i.val at hlow
  rw [S.wholeRowDegree_eq_neighborhood_mass i] at hlow
  have hI : MeasurableSet I := (S.hfibers i.val i.property).1
  have hJ : MeasurableSet J := S.measurableSet_cuspThreeMissingRegion i
  have hA : 0 < A :=
    ENNReal.toReal_pos (S.hfibers i.val i.property).2.1.ne' (measure_ne_top μ _)
  have hA0 : A ≠ 0 := hA.ne'
  have ht0 : t ≠ 0 := ht.ne'
  have hg : Integrable (g : Ω → ℝ) μ := (Lp.memLp g).integrable (by norm_num)
  obtain ⟨hmean, hconst, hdegree, hGenergy, hMenergy⟩ := missing_direction_data S i hW hd hgap
  change (∫ x, f x ∂μ) = 0 at hmean
  change (∫ x, g x * f x ∂μ) = t * μ.real N - ∫ x in J, g x ∂μ at hconst
  have hdegree' : (∫ x, g x * f x ∂μ) = v - 2 * z := by
    change (∫ x, g x * f x ∂μ) = v - ∫ p in J ×ˢ J,
      adjacencyKernel W p.1 p.2 ∂μ.prod μ at hdegree
    dsimp [z]
    linarith only [hdegree]
  have hGenergy' : kernelEnergy (μ := μ) (adjacencyKernel W) f = 2 * z := by
    dsimp [z]
    linarith only [hGenergy]
  change kernelEnergy (μ := μ) (shiftedKernel W m) f = FJ at hMenergy
  have hL : 0 < v - 2 * z := by
    have hi : Integrable (fun x => μ.real N - g x) (μ.restrict J) :=
      (integrable_const _).sub hg.integrableOn
    have hnonneg : ∀ᵐ x ∂μ.restrict J, 0 ≤ μ.real N - g x :=
      hlow.mono (fun _ hx => sub_nonneg.mpr hx.2.le)
    have hne : (∫ x in J, μ.real N - g x ∂μ) ≠ 0 := by
      intro hz
      have hzero := (integral_eq_zero_iff_of_nonneg_ae hnonneg hi).mp hz
      have hJne : μ J ≠ 0 := by
        intro he
        have hreal : t = 0 := by dsimp [t, measureReal_def]; rw [he]; rfl
        exact ht0 hreal
      obtain ⟨x, _, hx, hxzero⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hJne (hlow.and hzero)
      change μ.real N - g x = 0 at hxzero
      have hxlt : g x < μ.real N := hx.2
      linarith only [hxlt, hxzero]
    have hpos := lt_of_le_of_ne (integral_nonneg_of_ae hnonneg) (Ne.symm hne)
    rw [integral_sub (integrable_const _) hg.integrableOn, setIntegral_const, smul_eq_mul] at hpos
    change 0 < t * μ.real N - ∫ x in J, g x ∂μ at hpos
    linarith only [hpos, hconst, hdegree']
  have hG : Integrable (fun p : Ω × Ω => adjacencyKernel W p.1 p.2) (μ.prod μ) := by
    simpa only [mul_one] using integrable_kernel_bilinear (adjacencyKernel_measurable W)
      (adjacencyKernel_bound W) (integrable_const (1 : ℝ)) (integrable_const (1 : ℝ))
  have hM : Integrable (fun p : Ω × Ω => shiftedKernel W m p.1 p.2) (μ.prod μ) := by
    simpa only [mul_one] using integrable_kernel_bilinear (shiftedKernel_measurable W m)
      (shiftedKernel_bound W m) (integrable_const (1 : ℝ)) (integrable_const (1 : ℝ))
  have hz : 0 ≤ z := div_nonneg (integral_nonneg (fun p => (adjacency_moment_mem W p).1)) (by norm_num)
  have hFJ : 0 ≤ FJ := integral_nonneg_of_ae (ae_restrict_of_ae
    (hW.moment_mem.mono (fun _ hx => hx.1)))
  have hcap : FJ ≤ 2 * (1 - m) * z := by
    have hbound : ∀ᵐ p ∂μ.prod μ,
        shiftedKernel W m p.1 p.2 ≤ (1 - m) * adjacencyKernel W p.1 p.2 := by
      apply Eventually.of_forall
      intro p
      have hc := charge_moment_le_adjacency W p
      have he := shiftedMoment_eq W m p
      change shiftedMoment W m p ≤ (1 - m) * W.moment CappedColor.adjacency p
      linarith only [hc, he]
    have hpaid : (∫ p in J ×ˢ J, shiftedKernel W m p.1 p.2 ∂μ.prod μ) ≤
        ∫ p in J ×ˢ J, (1 - m) * adjacencyKernel W p.1 p.2 ∂μ.prod μ :=
      integral_mono_ae hM.integrableOn (hG.integrableOn.const_mul (1 - m))
        (ae_restrict_of_ae hbound)
    rw [integral_const_mul] at hpaid
    dsimp [FJ, z]
    nlinarith only [hpaid]
  have hpositive (hzpos : 0 < z) : 0 < FJ := by
    by_contra hn
    have he : FJ = 0 := le_antisymm (le_of_not_gt hn) hFJ
    have hzero := (integral_eq_zero_iff_of_nonneg_ae
      (ae_restrict_of_ae (hW.moment_mem.mono (fun _ hx => hx.1))) hM.integrableOn).mp he
    have hGzero : ∀ᵐ p ∂(μ.prod μ).restrict (J ×ˢ J), adjacencyKernel W p.1 p.2 = 0 := by
      filter_upwards [hzero, ae_restrict_of_ae (hW.strict_gap_structure hd hgap).strict_support]
        with p hz hs
      change adjacencyKernel W p.1 p.2 = if 0 < shiftedKernel W m p.1 p.2 then 1 else 0 at hs
      change shiftedKernel W m p.1 p.2 = 0 at hz
      simpa only [hz, lt_self_iff_false, ite_false] using hs
    have hz0 : z = 0 := by dsimp [z]; rw [integral_eq_zero_of_ae hGzero]; norm_num
    linarith only [hzpos, hz0]
  have hreturn (hzpos : 0 < z) : (2 + A / t) * z < v := by
    let a := A / t
    let w := fun x => J.indicator (fun _ => a) x - I.indicator (fun _ => (1 : ℝ)) x
    have ha : 0 < a := div_pos hA ht
    have ha0 : a ≠ 0 := ha.ne'
    have hz0 : z ≠ 0 := hzpos.ne'
    have hw : Integrable w μ := ((integrable_const a).indicator hJ).sub ((integrable_const 1).indicator hI)
    have hscale : w = fun x => -a * f x := by
      funext x
      change J.indicator (fun _ => a) x - I.indicator (fun _ => (1 : ℝ)) x =
        -a * (t * I.indicator (fun _ => A⁻¹) x - J.indicator (fun _ => (1 : ℝ)) x)
      by_cases hxI : x ∈ I <;> by_cases hxJ : x ∈ J <;> simp [hxI, hxJ]
      all_goals dsimp [a]
      all_goals field_simp
      all_goals ring
    have hwm : (∫ x, w x ∂μ) = 0 := by rw [hscale, integral_const_mul, hmean, mul_zero]
    have hbelow : ∀ᵐ x ∂μ, -1 ≤ w x := by
      apply Eventually.of_forall
      intro x
      have hnonneg : 0 ≤ J.indicator (fun _ => a) x := indicator_nonneg (fun _ _ => ha.le) x
      have hone : I.indicator (fun _ => (1 : ℝ)) x ≤ 1 := by
        by_cases hx : x ∈ I <;> simp [hx]
      change -1 ≤ J.indicator (fun _ => a) x - I.indicator (fun _ => (1 : ℝ)) x
      linarith only [hnonneg, hone]
    have henergy_scale (K : Ω → Ω → ℝ) :
        kernelEnergy (μ := μ) K w = a ^ 2 * kernelEnergy (μ := μ) K f := by
      rw [hscale, kernelEnergy, kernelEnergy, ← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall (fun p => by ring)
    have hwG : kernelEnergy (μ := μ) (adjacencyKernel W) w = a ^ 2 * (2 * z) := by
      rw [henergy_scale, hGenergy']
    have hwM : 0 < kernelEnergy (μ := μ) (shiftedKernel W m) w := by
      rw [henergy_scale, hMenergy]
      exact mul_pos (sq_pos_of_pos ha) (hpositive hzpos)
    have hwd : (∫ x, g x * w x ∂μ) = -a * (v - 2 * z) := by
      have he : (fun x => g x * w x) = fun x => -a * (g x * f x) := by
        rw [hscale]
        funext x
        ring
      rw [he, integral_const_mul, hdegree']
    by_contra hn
    have hbound : v - 2 * z ≤ a * z := by dsimp [a]; linarith only [le_of_not_gt hn]
    let tau := (v - 2 * z) / (a * z)
    have htau : tau ∈ Icc (0 : ℝ) 1 :=
      ⟨(div_pos hL (mul_pos ha hzpos)).le, (div_le_one (mul_pos ha hzpos)).mpr hbound⟩
    have htaupos : 0 < tau := div_pos hL (mul_pos ha hzpos)
    apply hW.no_density_return_of_positive_energy w hw hwm hbelow hwM tau htau htaupos
    rw [density_integrableTilt, hW.density_eq, hwd, hwG]
    dsimp [tau]
    field_simp
    ring
  refine ⟨hz, hFJ, hL, (fun hzpos => ⟨hpositive hzpos, hreturn hzpos⟩), ?_, hcap⟩
  intro hz0
  change z = 0 at hz0
  change FJ = 0 ∧ 0 < v
  refine ⟨by rw [hz0] at hcap; nlinarith only [hcap, hFJ], ?_⟩
  rw [hz0] at hL
  linarith only [hL]

end Erdos1017.CappedModel.SelectedHighLowStructure
