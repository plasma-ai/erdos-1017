module

public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2PrivateCovariance
public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2PrivateRootStar
public import Erdos1017.SelectedModel.Structure.DegreeSetAverages
public import Erdos1017.Exclusions.Common.Saturation.SelectedSaturatedScoreFloor
public import Erdos1017.SelectedModel.Flows.SelectedAtomRedirection

/-!
# Private-hole geometry for the covariance tangent

The private hole of the second whole atom lies in the original high class almost
everywhere, since the first high fiber forces the second fiber low
(`ae_private_hole_high`), and the private-row geometry supplies every degree
input to the original-model covariance tangent
(`private_covariance_of_private_hole`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Classical RealInnerProductSpace

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem wholeRowDegree_eq_rootNeighborhood
    (S : SelectedHighLowStructure W m) (r : S.I) :
    wholeRowDegree r.val = μ.real (S.rootNeighborhood r) := by
  have hN := S.measurableSet_rootNeighborhood r
  have heq : (fun x => if 0 < (r.val : Ω → ℝ) x then (1 : ℝ) else 0) =ᵐ[μ]
      (S.rootNeighborhood r).indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [S.ae_rootNeighborhood_iff r] with x hx
    by_cases hr : 0 < (r.val : Ω → ℝ) x
    · simp [hr, (hx.mpr hr)]
    · simp [hr, (not_iff_not.mpr hx).mpr hr]
  rw [wholeRowDegree, integral_congr_ae heq]
  exact integral_indicator_one hN

private theorem ae_private_second_root_off_first
    (S : SelectedHighLowStructure W m) (i p : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hprivate : ∀ᵐ q ∂μ.prod μ, S.ρ q.1 = i.val →
      adjacencyKernel W q.1 q.2 =
        if S.ρ q.2 = i.val ∨ S.ρ q.2 = p.val then 0 else 1) :
    ∀ᵐ y ∂μ.restrict {x | S.ρ x = i.val}, y ∉ S.rootNeighborhood p := by
  let I := {x | S.ρ x = i.val}
  let P := {x | S.ρ x = p.val}
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving
  have hpair : ∀ᵐ q ∂μ.prod μ, q.1 ∈ P → q.2 ∈ I →
      q.2 ∉ S.rootNeighborhood p := by
    filter_upwards [hswap.ae hprivate, adjacencyKernel_symm W,
      PhysicalRepresentative.adjacency_moment_ae_eq W m
        (hW.strict_gap_structure hd hgap).strict_support,
      S.ae_root_adjacency p hW hd hgap] with q hpriv hsym hphys hroot hp hi hn
    have hzero := hpriv hi
    change adjacencyKernel W q.2 q.1 =
      (if S.ρ q.1 = i.val ∨ S.ρ q.1 = p.val then 0 else 1) at hzero
    have hp' : S.ρ q.1 = p.val := hp
    simp only [hp', or_true, ite_true] at hzero
    have hz : adjacencyKernel W q.1 q.2 = 0 := hsym.trans hzero
    have hfalse : PhysicalRepresentative.adjacency W m q.1 q.2 = false := by
      cases he : PhysicalRepresentative.adjacency W m q.1 q.2
      · rfl
      · have hphys' := hphys
        simp only [he, ↓reduceIte] at hphys'
        change adjacencyKernel W q.1 q.2 = 1 at hphys'
        exact False.elim (by linarith only [hz, hphys'])
    have htrue := (hroot hp).mpr hn
    rw [hfalse] at htrue
    cases htrue
  obtain ⟨x, hx, hgood⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers p.val p.property).2.1.ne'
    ((ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hpair)).and
      (ae_restrict_mem (S.hfibers p.val p.property).1))
  filter_upwards [ae_restrict_of_ae hgood.1,
    ae_restrict_mem (S.hfibers i.val i.property).1] with y hy hi
  exact hy hgood.2 hi

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
private theorem ae_whole_row_zero_off_root
    (S : SelectedHighLowStructure W m) (r : S.I)
    (T : Set Ω)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hoff : ∀ᵐ x ∂μ.restrict T, x ∉ S.rootNeighborhood r) :
    ∀ᵐ x ∂μ.restrict T, (r.val : Ω → ℝ) x = 0 := by
  filter_upwards [hoff, ae_restrict_of_ae (S.ae_rootNeighborhood_iff r),
    ae_restrict_of_ae (S.ae_whole_row_nonneg r hW)] with x hx hiff hnonneg
  exact le_antisymm (le_of_not_gt (fun h => hx (hiff.mpr h))) hnonneg

private theorem ae_private_second_row_zero_first
    (S : SelectedHighLowStructure W m) (i p : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hprivate : ∀ᵐ q ∂μ.prod μ, S.ρ q.1 = i.val →
      adjacencyKernel W q.1 q.2 =
        if S.ρ q.2 = i.val ∨ S.ρ q.2 = p.val then 0 else 1) :
    ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, (p.val : Ω → ℝ) x = 0 :=
  S.ae_whole_row_zero_off_root p _ hW
    (S.ae_private_second_root_off_first i p hW hd hgap hprivate)

private theorem private_wholeRowDegrees
    (S : SelectedHighLowStructure W m) (i p : S.I) (hip : i ≠ p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hprivate : ∀ᵐ q ∂μ.prod μ, S.ρ q.1 = i.val →
      adjacencyKernel W q.1 q.2 =
        if S.ρ q.2 = i.val ∨ S.ρ q.2 = p.val then 0 else 1) :
    let I := {x | S.ρ x = i.val}
    let P := {x | S.ρ x = p.val}
    let E := I ∪ P
    let K := Eᶜ \ S.rootNeighborhood p
    wholeRowDegree i.val = 1 - μ.real I - μ.real P ∧
      wholeRowDegree p.val = 1 - μ.real I - μ.real P - μ.real K := by
  let I := {x | S.ρ x = i.val}
  let P := {x | S.ρ x = p.val}
  let E := I ∪ P
  let N := S.rootNeighborhood p
  let K := Eᶜ \ N
  have hI : MeasurableSet I := (S.hfibers i.val i.property).1
  have hP : MeasurableSet P := (S.hfibers p.val p.property).1
  have hE : MeasurableSet E := hI.union hP
  have hN : MeasurableSet N := S.measurableSet_rootNeighborhood p
  have hK : MeasurableSet K := hE.compl.diff hN
  have hdis : Disjoint I P := disjoint_left.mpr (fun _ hi hp =>
    hip (Subtype.ext (hi.symm.trans hp)))
  have hNi : S.rootNeighborhood i =ᵐ[μ] Eᶜ :=
    (S.ae_private_rootNeighborhood_iff i p hW hd hgap hprivate).mono
      (fun _ hx => propext (by simpa only [E, I, P, mem_compl_iff, mem_union,
        mem_ofPred_eq, not_or] using hx))
  have hNpI := S.ae_private_second_root_off_first i p hW hd hgap hprivate
  have hNpE : ∀ᵐ x ∂μ, x ∈ N → x ∉ E := by
    filter_upwards [(ae_restrict_iff' hI).mp hNpI] with x hx hn he
    rcases he with hi | hp
    · exact hx hi hn
    · exact Set.disjoint_left.mp (S.rootNeighborhood_disjoint p) hp hn
  have hclip : N =ᵐ[μ] Eᶜ ∩ N := by
    filter_upwards [hNpE] with x hx
    exact propext ⟨(fun hn => ⟨hx hn, hn⟩), And.right⟩
  have hunion : Eᶜ = (Eᶜ ∩ N) ∪ K := by
    ext x
    simp only [K, mem_compl_iff, mem_union, mem_inter_iff, Set.mem_sdiff]
    tauto
  have hdis' : Disjoint (Eᶜ ∩ N) K := disjoint_left.mpr (fun _ hx hy => hy.2 hx.2)
  have hEreal : μ.real Eᶜ = 1 - μ.real I - μ.real P := by
    rw [measureReal_compl hE, probReal_univ, measureReal_union hdis hP]
    ring
  have hNreal : μ.real N = 1 - μ.real I - μ.real P - μ.real K := by
    have hpart : μ.real Eᶜ = μ.real (Eᶜ ∩ N) + μ.real K := by
      calc
        μ.real Eᶜ = μ.real ((Eᶜ ∩ N) ∪ K) := congrArg μ.real hunion
        _ = μ.real (Eᶜ ∩ N) + μ.real K :=
          measureReal_union hdis' hK (measure_ne_top μ _) (measure_ne_top μ _)
    rw [← measureReal_congr hclip] at hpart
    linarith [hEreal]
  constructor
  · rw [S.wholeRowDegree_eq_rootNeighborhood i, measureReal_congr hNi]
    exact hEreal
  · rw [S.wholeRowDegree_eq_rootNeighborhood p]
    exact hNreal

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem adjacency_inner_normalizedHead
    (S : SelectedHighLowStructure W m) (r : S.I) :
    ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), S.normalizedHead r⟫ =
      wholeRowDegree r.val := by
  rw [real_inner_comm]
  exact KernelOperator.normalizedSetL2_inner_of_constant _ _
    (S.hfibers r.val r.property).2.1 _ _
    (wholeRowFiber_degree W m S.ρ r.val (S.hfibers r.val r.property).2.2.2)

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem adjacency_inner_one {d c : ℝ}
    (hW : FullStationaryClass d c W m) :
    ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), Lp.const 2 μ (1 : ℝ)⟫ =
      2 * d := by
  rw [← weighted_adjacency_eq, weightedPairIntegral_one]
  have hdW := hW.density_eq
  unfold density at hdW
  change (∫ q, adjacencyKernel W q.1 q.2 ∂μ.prod μ) / 2 = d at hdW
  linarith

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
private theorem ae_zero_rect_of_row_zero
    (S : SelectedHighLowStructure W m) (p : S.I)
    (T : Set Ω)
    (hzero : ∀ᵐ x ∂μ.restrict T, (p.val : Ω → ℝ) x = 0) :
    ∀ᵐ q ∂(μ.restrict {x | S.ρ x = p.val}).prod (μ.restrict T),
      shiftedKernel W m q.1 q.2 = 0 := by
  have hle : (μ.restrict {x | S.ρ x = p.val}).prod (μ.restrict T) ≤ μ.prod μ :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  filter_upwards [ae_mono hle (S.ae_kernel_eq_fiber_row p.val p.property),
    Measure.quasiMeasurePreserving_fst.ae
      (ae_restrict_mem (S.hfibers p.val p.property).1),
    Measure.quasiMeasurePreserving_snd.ae hzero] with q hrow hp hz
  exact (hrow hp).trans hz

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem normalizedSetL2_inner_le_of_ae_le (s : Set Ω)
    (hs : MeasurableSet s) (hspos : 0 < μ s) (f : Lp ℝ 2 μ) (a : ℝ)
    (hf : ∀ᵐ x ∂μ.restrict s, f x ≤ a) :
    ⟪f, KernelOperator.normalizedSetL2 s hs⟫ ≤ a := by
  have hi : Integrable (fun x => f x) (μ.restrict s) :=
    ((Lp.memLp f).integrable (by norm_num)).integrableOn
  have hint := integral_mono_ae hi (integrable_const a) hf
  have hmasspos : 0 < μ.real s := ENNReal.toReal_pos hspos.ne' (measure_ne_top μ _)
  rw [setIntegral_const, smul_eq_mul] at hint
  rw [real_inner_comm, KernelOperator.normalizedSetL2_inner]
  calc
    _ ≤ (μ.real s)⁻¹ * (μ.real s * a) :=
      mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hmasspos.le)
    _ = a := by field_simp

private theorem ae_private_second_low
    (S : SelectedHighLowStructure W m) (i p : S.I) (hip : i ≠ p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.H)
    (hprivate : ∀ᵐ q ∂μ.prod μ, S.ρ q.1 = i.val →
      adjacencyKernel W q.1 q.2 =
        if S.ρ q.2 = i.val ∨ S.ρ q.2 = p.val then 0 else 1) :
    ∀ᵐ x ∂μ.restrict {x | S.ρ x = p.val}, x ∈ S.L := by
  let I := {x | S.ρ x = i.val}
  let P := {x | S.ρ x = p.val}
  have hI := (S.hfibers i.val i.property).1
  have hP := (S.hfibers p.val p.property).1
  have hNi := S.ae_private_rootNeighborhood_iff i p hW hd hgap hprivate
  have hiOff : ∀ᵐ x ∂μ.restrict P, x ∉ S.rootNeighborhood i := by
    filter_upwards [ae_restrict_of_ae hNi, ae_restrict_mem hP] with x hx hp hn
    exact (hx.mp hn).2 hp
  have hirowP := S.ae_whole_row_zero_off_root i P hW hiOff
  have hzero := S.ae_zero_rect_of_row_zero i P hirowP
  have hle : (μ.restrict I).prod (μ.restrict P) ≤ μ.prod μ :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  have hprod : ∀ᵐ q ∂(μ.restrict I).prod (μ.restrict P), q.2 ∈ S.L := by
    filter_upwards [hzero, ae_mono hle S.hrelation,
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hI),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hP),
      Measure.quasiMeasurePreserving_fst.ae hhigh]
      with q hz hrel hi hp hhi
    have hneq : S.ρ q.1 ≠ S.ρ q.2 := by
      intro he
      exact hip (Subtype.ext (hi.symm.trans (he.trans hp)))
    rcases hrel ⟨hz, hneq⟩ with h | h
    · exact h.2.1
    · exact False.elim (Set.disjoint_left.mp S.hpartition.2.2.2.2.1 hhi h.2.1)
  obtain ⟨x, _, hsec⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers i.val i.property).2.1.ne'
    ((Measure.ae_ae_of_ae_prod hprod).and (ae_restrict_mem hI))
  exact hsec.1

/-- The actual private hole of the second whole atom lies in the original
HIGH class almost everywhere. The first HIGH fiber forces the second fiber
LOW, and the original missing second-to-hole relation reverses that order. -/
theorem ae_private_hole_high
    (S : SelectedHighLowStructure W m) (i p : S.I) (hip : i ≠ p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.H)
    (hprivate : ∀ᵐ q ∂μ.prod μ, S.ρ q.1 = i.val →
      adjacencyKernel W q.1 q.2 =
        if S.ρ q.2 = i.val ∨ S.ρ q.2 = p.val then 0 else 1) :
    ∀ᵐ x ∂μ.restrict (({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ \
      S.rootNeighborhood p), x ∈ S.H := by
  let P := {x | S.ρ x = p.val}
  let K := ({x | S.ρ x = i.val} ∪ P)ᶜ \ S.rootNeighborhood p
  have hP := (S.hfibers p.val p.property).1
  have hPpos := (S.hfibers p.val p.property).2.1
  have hK : MeasurableSet K :=
    ((S.hfibers i.val i.property).1.union hP).compl.diff
      (S.measurableSet_rootNeighborhood p)
  have hlow := S.ae_private_second_low i p hip hW hd hgap hhigh hprivate
  have hOff : ∀ᵐ x ∂μ.restrict K, x ∉ S.rootNeighborhood p :=
    (ae_restrict_mem hK).mono (fun _ hx => hx.2)
  have hpzero := S.ae_whole_row_zero_off_root p K hW hOff
  have hzero := S.ae_zero_rect_of_row_zero p K hpzero
  have hle : (μ.restrict P).prod (μ.restrict K) ≤ μ.prod μ :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  have hprod : ∀ᵐ q ∂(μ.restrict P).prod (μ.restrict K), q.2 ∈ S.H := by
    filter_upwards [hzero, ae_mono hle S.hrelation,
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hP),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hK),
      Measure.quasiMeasurePreserving_fst.ae hlow]
      with q hz hrel hp hk hLp
    have hneq : S.ρ q.1 ≠ S.ρ q.2 := by
      intro he
      exact hk.1 (Or.inr (he.symm.trans hp))
    rcases hrel ⟨hz, hneq⟩ with h | h
    · exact False.elim (Set.disjoint_left.mp S.hpartition.2.2.2.2.1 h.1 hLp)
    · exact h.1
  obtain ⟨x, _, hsec⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    hPpos.ne' ((Measure.ae_ae_of_ae_prod hprod).and (ae_restrict_mem hP))
  exact hsec.1

private theorem private_hole_degree_gt_second
    (S : SelectedHighLowStructure W m) (i p : S.I) (hip : i ≠ p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.H)
    (hprivate : ∀ᵐ q ∂μ.prod μ, S.ρ q.1 = i.val →
      adjacencyKernel W q.1 q.2 =
        if S.ρ q.2 = i.val ∨ S.ρ q.2 = p.val then 0 else 1)
    (hk : 0 < μ (({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ \
      S.rootNeighborhood p)) :
    let K := ({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ \
      S.rootNeighborhood p
    ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), S.normalizedHead p⟫ <
      ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)),
        KernelOperator.normalizedSetL2 K ((S.hfibers i.val i.property).1.union
          (S.hfibers p.val p.property).1 |>.compl.diff
            (S.measurableSet_rootNeighborhood p))⟫ := by
  let I := {x | S.ρ x = i.val}
  let P := {x | S.ρ x = p.val}
  let E := I ∪ P
  let K := Eᶜ \ S.rootNeighborhood p
  let g := adjacencyOperator W (Lp.const 2 μ (1 : ℝ))
  have hP := (S.hfibers p.val p.property).1
  have hPpos := (S.hfibers p.val p.property).2.1
  have hK : MeasurableSet K :=
    ((S.hfibers i.val i.property).1.union hP).compl.diff
      (S.measurableSet_rootNeighborhood p)
  have hhighK := S.ae_private_hole_high i p hip hW hd hgap hhigh hprivate
  have hOff : ∀ᵐ x ∂μ.restrict K, x ∉ S.rootNeighborhood p :=
    (ae_restrict_mem hK).mono (fun _ hx => hx.2)
  have hpzero := S.ae_whole_row_zero_off_root p K hW hOff
  have hzero := S.ae_zero_rect_of_row_zero p K hpzero
  have hle : (μ.restrict P).prod (μ.restrict K) ≤ μ.prod μ :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  have horder : ∀ᵐ q ∂(μ.restrict P).prod (μ.restrict K), g q.1 < g q.2 := by
    filter_upwards [hzero, ae_mono hle S.hrelation,
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hP),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hK),
      Measure.quasiMeasurePreserving_snd.ae hhighK]
      with q hz hrel hp hk' hHk
    have hneq : S.ρ q.1 ≠ S.ρ q.2 := by
      intro he
      exact hk'.1 (Or.inr (he.symm.trans hp))
    rcases hrel ⟨hz, hneq⟩ with h | h
    · exact False.elim (Set.disjoint_left.mp S.hpartition.2.2.2.2.1 hHk h.2.1)
    · exact h.2.2
  have hsec := Measure.ae_ae_of_ae_prod horder
  have hlt : ∀ᵐ x ∂μ.restrict P,
      g x < ⟪g, KernelOperator.normalizedSetL2 K hK⟫ :=
    hsec.mono (fun x hx =>
      KernelOperator.normalizedSetL2_inner_gt_of_ae_gt K hK hk g (g x) hx)
  exact KernelOperator.normalizedSetL2_inner_lt_of_ae_lt P hP hPpos g _ hlt

private theorem private_hole_degree_le_one_sub_second_mass
    (S : SelectedHighLowStructure W m) (i p : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hk : 0 < μ (({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ \
      S.rootNeighborhood p)) :
    let K := ({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ \
      S.rootNeighborhood p
    ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)),
      KernelOperator.normalizedSetL2 K ((S.hfibers i.val i.property).1.union
        (S.hfibers p.val p.property).1 |>.compl.diff
          (S.measurableSet_rootNeighborhood p))⟫ ≤
        1 - μ.real {x | S.ρ x = p.val} := by
  let P := {x | S.ρ x = p.val}
  let K := ({x | S.ρ x = i.val} ∪ P)ᶜ \ S.rootNeighborhood p
  let g := adjacencyOperator W (Lp.const 2 μ (1 : ℝ))
  have hP := (S.hfibers p.val p.property).1
  have hK : MeasurableSet K :=
    ((S.hfibers i.val i.property).1.union hP).compl.diff
      (S.measurableSet_rootNeighborhood p)
  have hOff : ∀ᵐ x ∂μ.restrict K, x ∉ S.rootNeighborhood p :=
    (ae_restrict_mem hK).mono (fun _ hx => hx.2)
  have hpzero := S.ae_whole_row_zero_off_root p K hW hOff
  have hzero := S.ae_zero_rect_of_row_zero p K hpzero
  have hAdjPK : ∀ᵐ q ∂(μ.restrict P).prod (μ.restrict K),
      adjacencyKernel W q.1 q.2 = 0 := by
    have hle : (μ.restrict P).prod (μ.restrict K) ≤ μ.prod μ :=
      Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
    filter_upwards [hzero,
      ae_mono hle (hW.strict_gap_structure hd hgap).strict_support] with q hz hs
    change adjacencyKernel W q.1 q.2 =
      (if 0 < shiftedKernel W m q.1 q.2 then 1 else 0) at hs
    rw [hz] at hs
    simpa only [lt_irrefl, ↓reduceIte] using hs
  have hswap := (Measure.measurePreserving_swap
    (μ := μ.restrict K) (ν := μ.restrict P)).quasiMeasurePreserving
  have hAdjKP : ∀ᵐ q ∂(μ.restrict K).prod (μ.restrict P),
      adjacencyKernel W q.1 q.2 = 0 := by
    have hle : (μ.restrict K).prod (μ.restrict P) ≤ μ.prod μ :=
      Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
    filter_upwards [hswap.ae hAdjPK, ae_mono hle (adjacencyKernel_symm W)]
      with q hz hs
    change adjacencyKernel W q.2 q.1 = 0 at hz
    exact hs.trans hz
  have hsec := Measure.ae_ae_of_ae_prod hAdjKP
  have hbound : ∀ᵐ x ∂μ.restrict K, g x ≤ 1 - μ.real P := by
    filter_upwards [hsec,
      ae_restrict_of_ae (KernelOperator.onL2_coe (adjacencyKernel W)
        (adjacencyKernel_measurable W) (adjacencyKernel_bound W)
        (Lp.const 2 μ (1 : ℝ)))] with x hx hg
    have hzeroP := (ae_restrict_iff' hP).mp hx
    have hpoint : ∀ᵐ y ∂μ,
        adjacencyKernel W x y ≤ 1 - P.indicator (fun _ => (1 : ℝ)) y := by
      filter_upwards [hzeroP] with y hy
      by_cases hp : y ∈ P
      · rw [hy hp, indicator_of_mem hp]
        norm_num
      · simp only [indicator_of_notMem hp, sub_zero]
        exact (adjacency_moment_mem W (x, y)).2
    have hi : Integrable (adjacencyKernel W x) μ := Integrable.of_bound
      ((W.stronglyMeasurable_moment
        CappedColor.continuous_adjacency.measurable.stronglyMeasurable).comp_measurable
          (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
      (Eventually.of_forall (fun y => by
        change ‖W.moment CappedColor.adjacency (x, y)‖ ≤ 1
        rw [Real.norm_eq_abs, abs_of_nonneg (adjacency_moment_mem W (x, y)).1]
        exact (adjacency_moment_mem W (x, y)).2))
    have hiP : Integrable (P.indicator (fun _ => (1 : ℝ))) μ :=
      (integrable_const 1).indicator hP
    have hle' := integral_mono_ae hi ((integrable_const 1).sub hiP) hpoint
    change (∫ y, adjacencyKernel W x y ∂μ) ≤
      ∫ y, (1 : ℝ) - P.indicator (fun _ => (1 : ℝ)) y ∂μ at hle'
    rw [integral_sub (integrable_const 1) hiP, integral_const, probReal_univ,
      one_smul] at hle'
    have hiPeq : (∫ y, P.indicator (fun _ => (1 : ℝ)) y ∂μ) = μ.real P :=
      integral_indicator_one hP
    rw [hiPeq] at hle'
    have hgeq : g x = ∫ y, adjacencyKernel W x y ∂μ := by
      change g x = KernelOperator.applyKernel (adjacencyKernel W)
        (Lp.const 2 μ (1 : ℝ)) x at hg
      rw [hg, KernelOperator.applyKernel]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_const 2 μ (1 : ℝ)] with y hy
      simp only [hy, Function.const_apply, mul_one]
    rw [hgeq]
    exact hle'
  exact normalizedSetL2_inner_le_of_ae_le K hK hk g _ hbound

/-- The actual private-row geometry supplies every degree input to the
original-model covariance tangent, including strict order on the private hole. -/
theorem private_covariance_of_private_hole
    (S : SelectedHighLowStructure W m) (i p : S.I) (hip : i ≠ p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.H)
    (hprivate : ∀ᵐ q ∂μ.prod μ, S.ρ q.1 = i.val →
      adjacencyKernel W q.1 q.2 =
        if S.ρ q.2 = i.val ∨ S.ρ q.2 = p.val then 0 else 1)
    (hnA : 1 - 2 * d < μ.real {x | S.ρ x = i.val})
    (hk : 0 < μ (({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ \
      S.rootNeighborhood p))
    (hE : μ.real (({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ \
      S.rootNeighborhood p) <
      ∫ z in (({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ \
        S.rootNeighborhood p), (i.val : Ω → ℝ) z ∂μ) :
    let A := μ.real {x | S.ρ x = i.val}
    let b := μ.real {x | S.ρ x = p.val}
    let k := μ.real (({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ \
      S.rootNeighborhood p)
    (A + b + k - (1 - 2 * d)) ^ 2 < 2 * (2 * (c - m * d)) * k * (A + k) := by
  let I := {x | S.ρ x = i.val}
  let P := {x | S.ρ x = p.val}
  let K := (I ∪ P)ᶜ \ S.rootNeighborhood p
  let A := μ.real I
  let b := μ.real P
  let k := μ.real K
  let g := adjacencyOperator W (Lp.const 2 μ (1 : ℝ))
  have hK : MeasurableSet K :=
    ((S.hfibers i.val i.property).1.union (S.hfibers p.val p.property).1).compl.diff
      (S.measurableSet_rootNeighborhood p)
  let z := KernelOperator.normalizedSetL2 (μ := μ) K hK
  have hkreal : 0 < k := ENNReal.toReal_pos hk.ne' (measure_ne_top μ K)
  have hdegrees := S.private_wholeRowDegrees i p hip hW hd hgap hprivate
  have hdegI : wholeRowDegree i.val = 1 - A - b := hdegrees.1
  have hdegP : wholeRowDegree p.val = 1 - A - b - k := hdegrees.2
  have hgi : ⟪g, S.normalizedHead i⟫ = wholeRowDegree i.val :=
    S.adjacency_inner_normalizedHead i
  have hgp : ⟪g, S.normalizedHead p⟫ = wholeRowDegree p.val :=
    S.adjacency_inner_normalizedHead p
  have hge : ⟪g, Lp.const 2 μ (1 : ℝ)⟫ = 2 * d :=
    adjacency_inner_one hW
  have hgt : ⟪g, S.normalizedHead p⟫ < ⟪g, z⟫ :=
    S.private_hole_degree_gt_second i p hip hW hd hgap hhigh hprivate hk
  have hupper : ⟪g, z⟫ ≤ 1 - b :=
    S.private_hole_degree_le_one_sub_second_mass i p hW hd hgap hk
  have hPI := S.ae_private_second_row_zero_first i p hW hd hgap hprivate
  have hPK : ∀ᵐ x ∂μ.restrict K, (p.val : Ω → ℝ) x = 0 :=
    S.ae_whole_row_zero_off_root p K hW
      ((ae_restrict_mem hK).mono (fun _ hx => hx.2))
  let D := A + b + k - (1 - 2 * d)
  let DK := k * ⟪g, z - S.normalizedHead p⟫
  have hD : D = ⟪g, Lp.const 2 μ (1 : ℝ) - S.normalizedHead p⟫ := by
    rw [inner_sub_right, hge, hgp, hdegP]
    dsimp [D]
    ring
  have hDpos : 0 < D := by
    have hb0 : 0 ≤ b := measureReal_nonneg
    dsimp [D]
    linarith [hnA, hkreal]
  have hDI : ⟪g, S.normalizedHead i - S.normalizedHead p⟫ = k := by
    rw [inner_sub_right, hgi, hgp, hdegI, hdegP]
    ring
  have hDKpos : 0 < DK := by
    dsimp [DK]
    rw [inner_sub_right]
    exact mul_pos hkreal (sub_pos.mpr hgt)
  have hDKupper : DK ≤ k * (A + k) := by
    have hdiff : ⟪g, z - S.normalizedHead p⟫ ≤ A + k := by
      rw [inner_sub_right, hgp, hdegP]
      linarith [hupper]
    exact mul_le_mul_of_nonneg_left hdiff hkreal.le
  have hcov := S.private_covariance_necessary i p K hK hW hd hgap
    hPI hPK hk D DK hD hDpos hDI rfl hDKpos hDKupper hE
  simpa only [D, A, b, k, I, P, K] using hcov

end Erdos1017.CappedModel.SelectedHighLowStructure
