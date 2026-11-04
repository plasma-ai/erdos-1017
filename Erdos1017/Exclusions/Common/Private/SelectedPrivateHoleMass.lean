module

public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2PrivateRootStar
public import Erdos1017.SelectedModel.Saturation.SelectedSaturatedPairEnergy
public import Erdos1017.Exclusions.Common.Saturation.SelectedSaturatedScoreFloor

/-!
# Positive mass of the private hole

Every whole row has a positive physical neighborhood because its stationary row
integral is strictly positive, and a distinct whole private partner has a
positive exterior missing hole, since otherwise its degree would equal the first
root degree.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

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

/-- Every actual original whole row has a positive physical neighborhood
because its original stationary row integral is strictly positive. -/
theorem rootNeighborhood_measure_pos
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    0 < μ (S.rootNeighborhood r) := by
  by_contra hn
  have hz : μ (S.rootNeighborhood r) = 0 := le_antisymm (le_of_not_gt hn) zero_le
  have hnot : ∀ᵐ x ∂μ, x ∉ S.rootNeighborhood r :=
    measure_eq_zero_iff_ae_notMem.mp hz
  have hzero : ∀ᵐ x ∂μ, (r.val : Ω → ℝ) x = 0 := by
    filter_upwards [hnot, S.ae_rootNeighborhood_iff r, S.ae_whole_row_nonneg r hW]
      with x hn hi hp
    exact le_antisymm (le_of_not_gt (fun h => hn (hi.mpr h))) hp
  have hpos := (hW.strict_gap_structure hd hgap).stationary_pos
  rw [← S.row_integral_of_stationary r hW, integral_congr_ae hzero] at hpos
  simp at hpos

/-- A distinct whole private partner has a positive exterior missing
hole. Otherwise its original degree would equal the first root degree. -/
theorem private_hole_measure_pos
    (S : SelectedHighLowStructure W m) (i p : S.I) (hip : i ≠ p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hprivate : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      adjacencyKernel W z.1 z.2 =
        if S.ρ z.2 = i.val ∨ S.ρ z.2 = p.val then 0 else 1) :
    0 < μ (({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ \ S.rootNeighborhood p) := by
  let I := {x | S.ρ x = i.val}
  let P := {x | S.ρ x = p.val}
  let K := (I ∪ P)ᶜ \ S.rootNeighborhood p
  have hI : MeasurableSet I := (S.hfibers i.val i.property).1
  have hP : MeasurableSet P := (S.hfibers p.val p.property).1
  by_contra hk
  have hz : μ K = 0 := le_antisymm (le_of_not_gt hk) zero_le
  have hreal : μ.real K = 0 := by simp only [measureReal_def, hz, ENNReal.toReal_zero]
  have hdegrees := S.private_wholeRowDegrees i p hip hW hd hgap hprivate
  change wholeRowDegree i.val = 1 - μ.real I - μ.real P ∧
    wholeRowDegree p.val = 1 - μ.real I - μ.real P - μ.real K at hdegrees
  have heq : wholeRowDegree i.val = wholeRowDegree p.val := by
    rw [hreal] at hdegrees
    linarith only [hdegrees.1, hdegrees.2]
  have hzero : ∀ᵐ z ∂μ.prod μ, z.1 ∈ I → z.2 ∈ P → shiftedKernel W m z.1 z.2 = 0 := by
    filter_upwards [hprivate, (hW.strict_gap_structure hd hgap).strict_support,
      hW.moment_mem] with z hp hs hm hi hj
    have hA := hp hi
    simp only [show S.ρ z.2 = p.val from hj, or_true, ite_true] at hA
    change adjacencyKernel W z.1 z.2 =
      (if 0 < shiftedKernel W m z.1 z.2 then 1 else 0) at hs
    have hn : ¬0 < shiftedKernel W m z.1 z.2 := by
      intro hpos
      rw [ite_eq_left hpos] at hs
      linarith only [hA, hs]
    exact le_antisymm (le_of_not_gt hn) hm.1
  have hle : (μ.restrict I).prod (μ.restrict P) ≤ μ.prod μ :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  have hfalse : ∀ᵐ z ∂(μ.restrict I).prod (μ.restrict P), False := by
    filter_upwards [ae_mono hle hzero, ae_mono hle S.hdegreeNe,
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hI),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hP),
      Measure.quasiMeasurePreserving_fst.ae
        (wholeRowFiber_degree W m S.ρ i.val (S.hfibers i.val i.property).2.2.2),
      Measure.quasiMeasurePreserving_snd.ae
        (wholeRowFiber_degree W m S.ρ p.val (S.hfibers p.val p.property).2.2.2)]
      with z hz hn hi hp hgi hgp
    have hne : S.ρ z.1 ≠ S.ρ z.2 := fun he => hip (Subtype.ext (hi.symm.trans (he.trans hp)))
    exact (hn ⟨hz hi hp, hne⟩) (hgi.trans (heq.trans hgp.symm))
  obtain ⟨x, _, hx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers i.val i.property).2.1.ne' (Measure.ae_ae_of_ae_prod hfalse)
  obtain ⟨y, _, hy⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers p.val p.property).2.1.ne' hx
  exact hy

end Erdos1017.CappedModel.SelectedHighLowStructure
