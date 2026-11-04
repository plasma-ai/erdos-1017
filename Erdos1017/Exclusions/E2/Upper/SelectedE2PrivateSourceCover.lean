module

public import Erdos1017.Exclusions.Common.TwoCenter.SelectedTwoCenterDeficits
public import Erdos1017.Exclusions.Common.TwoCenter.SelectedTwoCenterHeadDegree
public import Erdos1017.Exclusions.Common.Saturation.SelectedSaturatedCommonNeighbors

/-!
# Vertex-cover bound on the private source deficit

`twoCenterPrivateDeficit`, `twoCenterPrivateThreshold` and `twoCenterPrivateLow`
describe the two-head shifted deficit, triangle charge threshold and strict-low
portion of a private source; the private source then has the fractional
vertex-cover lower bound, and a positive strict-low source concentrates in one
positive whole-row fiber (`exists_private_low_fiber`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical RealInnerProductSpace

namespace Erdos1017.CappedModel.SelectedHighLowStructure

private theorem exists_fiber_of_ae_pair_same
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (U : Set Ω) (hUpos : 0 < μ U)
    (ρ : Ω → ι) (I : Set ι)
    (hpair : ∀ᵐ p ∂(μ.restrict U).prod (μ.restrict U),
      ∃ i ∈ I, ρ p.1 = i ∧ ρ p.2 = i) :
    ∃ i ∈ I, ∀ᵐ x ∂μ.restrict U, ρ x = i := by
  have hsections := Measure.ae_ae_of_ae_prod hpair
  obtain ⟨x, _, hx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hUpos.ne' hsections
  obtain ⟨y, _, hy⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hUpos.ne' hx
  obtain ⟨i, hi, hxi, _⟩ := hy
  refine ⟨i, hi, ?_⟩
  filter_upwards [hx] with z hz
  obtain ⟨j, _, hxj, hzj⟩ := hz
  have hji : j = i := hxj.symm.trans hxi
  exact hzj.trans hji

private theorem integral_source_cover_of_low_subset
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (C A U : Set Ω) (hA : MeasurableSet A)
    (hU : MeasurableSet U) (hAC : A ⊆ C) (hUA : U ⊆ A)
    (hUpos : 0 < μ U) (f : Ω → ℝ) (hf : Integrable f μ)
    (ζ : ℝ)
    (hnonneg : ∀ᵐ x ∂μ.restrict U, 0 ≤ f x)
    (hlow : ∀ x ∈ U, f x < ζ / 2)
    (hrest : ∀ x ∈ C \ U, ζ / 2 ≤ f x)
    (hpair : ∀ᵐ y ∂μ.restrict (C \ A),
      ∀ᵐ x ∂μ.restrict U, ζ ≤ f x + f y) :
    ζ * min (μ.real C / 2) (μ.real C - μ.real A) ≤ ∫ x in C, f x ∂μ := by
  let s := μ.real C
  let σ := μ.real A
  let v := μ.real U
  let a := (∫ x in U, f x ∂μ) / v
  have hv : 0 < v := ENNReal.toReal_pos hUpos.ne' (measure_ne_top μ U)
  have hU_nonneg : 0 ≤ ∫ x in U, f x ∂μ := integral_nonneg_of_ae hnonneg
  have ha0 : 0 ≤ a := div_nonneg hU_nonneg hv.le
  have ha_le : a ≤ ζ / 2 := by
    have hi : (∫ x in U, f x ∂μ) ≤ (∫ x in U, ζ / 2 ∂μ) := by
      apply integral_mono_ae hf.restrict (integrable_const _)
      filter_upwards [ae_restrict_mem hU] with x hx
      exact (hlow x hx).le
    rw [setIntegral_const] at hi
    dsimp only [a]
    exact (div_le_iff₀ hv).mpr (by simpa only [smul_eq_mul, v, mul_comm] using hi)
  have hrest_a : ∀ᵐ x ∂μ.restrict (A \ U), a ≤ f x := by
    filter_upwards [ae_restrict_mem (hA.diff hU)] with x hx
    exact ha_le.trans (hrest x ⟨hAC hx.1, hx.2⟩)
  have hA_low : a * σ ≤ ∫ x in A, f x ∂μ := by
    have hi : (∫ x in A \ U, a ∂μ) ≤ (∫ x in A \ U, f x ∂μ) :=
      integral_mono_ae (integrable_const _) hf.restrict hrest_a
    rw [setIntegral_const, measureReal_sdiff hUA hU,
      setIntegral_sdiff hU hf.restrict hUA] at hi
    simp only [smul_eq_mul] at hi
    have hdiv : (∫ x in U, f x ∂μ) = a * v := by
      dsimp only [a]
      field_simp
    linarith only [hi, hdiv]
  have hpair_mean : ∀ᵐ y ∂μ.restrict (C \ A), ζ - a ≤ f y := by
    filter_upwards [hpair] with y hy
    have hi : (∫ x in U, ζ ∂μ) ≤ (∫ x in U, f x + f y ∂μ) := by
      apply integral_mono_ae (integrable_const _) (hf.restrict.add (integrable_const _))
      exact hy
    rw [setIntegral_const, integral_add hf.restrict (integrable_const _),
      setIntegral_const] at hi
    simp only [smul_eq_mul] at hi
    have hdiv : (∫ x in U, f x ∂μ) = a * v := by
      dsimp only [a]
      field_simp
    dsimp only [v] at hi hdiv
    have hv' : 0 < μ.real U := hv
    nlinarith only [hi, hdiv, hv']
  have houtside : (ζ - a) * (s - σ) ≤ ∫ x in C \ A, f x ∂μ := by
    have hi : (∫ x in C \ A, ζ - a ∂μ) ≤ (∫ x in C \ A, f x ∂μ) :=
      integral_mono_ae (integrable_const _) hf.restrict hpair_mean
    rw [setIntegral_const, measureReal_sdiff hAC hA] at hi
    simp only [smul_eq_mul] at hi
    nlinarith only [hi]
  have hwhole : (∫ x in C, f x ∂μ) =
      (∫ x in A, f x ∂μ) + (∫ x in C \ A, f x ∂μ) := by
    have hi := setIntegral_sdiff hA hf.restrict hAC
    linarith only [hi]
  have hσs : σ ≤ s := measureReal_mono hAC
  have hmin : ζ * min (s / 2) (s - σ) ≤ a * σ + (ζ - a) * (s - σ) := by
    by_cases hsmall : σ ≤ s / 2
    · have hmin' : min (s / 2) (s - σ) = s / 2 := min_eq_left (by linarith)
      rw [hmin']
      nlinarith only [ha0, ha_le, hsmall]
    · have hmin' : min (s / 2) (s - σ) = s - σ := min_eq_right (by linarith)
      rw [hmin']
      nlinarith only [ha0, hsmall]
  rw [hwhole]
  linarith only [hA_low, houtside, hmin]

private theorem tupleCharge_private_three {Ω : Type*} (Y : Ω → Ω → ℝ)
    (x y z : Ω) (hxy : Y x y = Y y x) (hxz : Y x z = Y z x)
    (hyz : Y y z = Y z y) :
    FiniteArity.tupleCharge Y ![x, y, z] = Y x y + Y x z + Y y z := by
  simp [FiniteArity.tupleCharge, FiniteArity.pairCharge,
    FiniteArity.crossSum, Fin.sum_univ_succ, hxy, hxz, hyz]
  ring

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}

/-- The original two-head shifted deficit at one original vertex. -/
def twoCenterPrivateDeficit (S : SelectedHighLowStructure W m) (r u : S.I) (x : Ω) : ℝ :=
  S.headPairing r u - r.val x - u.val x

/-- The original triangle charge threshold for a private source pair. -/
def twoCenterPrivateThreshold (S : SelectedHighLowStructure W m) (r u : S.I) : ℝ :=
  2 * S.headPairing r u - 1 + 3 * m

/-- The measurable strict-low portion of one original private source. -/
def twoCenterPrivateLow (S : SelectedHighLowStructure W m) (r u : S.I) : Set Ω :=
  S.twoCenterPrivate r u ∩
    {x | S.twoCenterPrivateDeficit r u x < S.twoCenterPrivateThreshold r u / 2}

theorem ReverseRecovery.measurableSet_twoCenterPrivateLow
    [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (R : S.ReverseRecovery) (r u : S.I) (hp : R.plateau = {r, u}) :
    MeasurableSet (S.twoCenterPrivateLow r u) := by
  have hdef : Measurable (S.twoCenterPrivateDeficit r u) := by
    unfold twoCenterPrivateDeficit
    fun_prop (disch := infer_instance)
  exact (R.measurableSet_twoCenter_patterns r u hp).1.inter
    (measurableSet_lt hdef measurable_const)

/-- Two distinct original rows inside one private HIGH source are present
in the original model. The only shifted-zero HIGH pairs are same-atom pairs. -/
theorem ae_private_cross_adjacency_one (r u : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m) :
    ∀ᵐ p ∂μ.prod μ, p.1 ∈ S.twoCenterPrivate r u →
      p.2 ∈ S.twoCenterPrivate r u →
      (∀ k ∈ S.I, S.ρ p.1 = k → S.ρ p.2 ≠ k) →
        adjacencyKernel W p.1 p.2 = 1 := by
  filter_upwards [hW.moment_mem, hW.complementary, S.hcoverage, S.hrelation]
    with p hmem hcomp hcover hrel hx hy hdiff
  have hpositive : 0 < shiftedKernel W m p.1 p.2 := by
    apply lt_of_le_of_ne hmem.1
    intro hzero
    rcases hcover hzero.symm with ⟨k, hk, hpk, hqk⟩ | hZ
    · exact hdiff k hk hpk hqk
    · rcases hrel hZ with h | h
      · exact disjoint_left.mp S.hpartition.2.2.2.2.1 hy.1.1.1 h.2.1
      · exact disjoint_left.mp S.hpartition.2.2.2.2.1 hx.1.1.1 h.2.1
  have hzero := (mul_eq_zero.mp hcomp).resolve_right (ne_of_gt hpositive)
  change 1 - adjacencyKernel W p.1 p.2 = 0 at hzero
  linarith only [hzero]

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- A genuine old triangle with the second head covers two present private
vertices by their original shifted deficits. -/
theorem ReverseRecovery.ae_private_pair_deficit_cover
    (R : S.ReverseRecovery) (r u : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hp : R.plateau = {r, u}) :
    ∀ᵐ p ∂μ.prod μ, p.1 ∈ S.twoCenterPrivate r u →
      p.2 ∈ S.twoCenterPrivate r u →
      (∀ k ∈ S.I, S.ρ p.1 = k → S.ρ p.2 ≠ k) →
        S.twoCenterPrivateThreshold r u ≤
          S.twoCenterPrivateDeficit r u p.1 + S.twoCenterPrivateDeficit r u p.2 := by
  let A := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  let Iu : Set Ω := {x | S.ρ x = u.val}
  have hu : u ∈ R.plateau := by rw [hp]; simp
  have hIupos : 0 < μ Iu := (S.hfibers u.val u.property).2.1
  have hs := hW.strict_gap_structure hd hgap
  have hfull := PhysicalRepresentative.full_feasible W hW.full m hs.strict_support hW.deterministic
  have hrows : ∀ᵐ z ∂μ.restrict Iu,
      (adjacencyKernel W z =ᵐ[μ] fun x => if 0 < u.val x then 1 else 0) ∧
      (chargeKernel W z =ᵐ[μ] fun x => u.val x + m * (if 0 < u.val x then 1 else 0)) := by
    simpa only [Iu] using
      ((S.hfibers u.val u.property).2.2.2.rows.mono (fun _ hx => hx.2))
  have hevent : ∀ᵐ p ∂μ.prod μ,
      Y p.1 p.2 = chargeKernel W p.1 p.2 ∧
      adjacencyKernel W p.1 p.2 = (if A p.1 p.2 = true then 1 else 0) := by
    filter_upwards [PhysicalRepresentative.charge_ae_eq W m hs.strict_support,
      PhysicalRepresentative.adjacency_moment_ae_eq W m hs.strict_support]
      with p hpY hpA
    exact ⟨hpY, hpA⟩
  have htest : ∀ᵐ v ∂Measure.pi (fun _ : Fin 3 => μ),
      FiniteArity.TupleClique A v → FiniteArity.tupleCharge Y v ≤ 1 := hfull 3
  have htrip : ∀ᵐ v ∂Measure.pi (fun _ : Fin 3 => μ),
      (FiniteArity.TupleClique A v → FiniteArity.tupleCharge Y v ≤ 1) ∧
      ∀ i j, i ≠ j →
        Y (v i) (v j) = chargeKernel W (v i) (v j) ∧
        adjacencyKernel W (v i) (v j) =
          (if A (v i) (v j) = true then 1 else 0) :=
    htest.and (FiniteArity.ae_all_pairs μ 3 _ hevent)
  have hroot := FiniteArity.ae_root_sections μ 2 _ htrip
  obtain ⟨z, hzIu, hzrows, hzroot⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hIupos.ne'
      (hrows.and (ae_restrict_of_ae hroot))
  have hpairSection : ∀ᵐ p ∂μ.prod μ,
      (FiniteArity.TupleClique A ![z, p.1, p.2] →
        FiniteArity.tupleCharge Y ![z, p.1, p.2] ≤ 1) ∧
      ∀ i j, i ≠ j →
        Y (![z, p.1, p.2] i) (![z, p.1, p.2] j) =
          chargeKernel W (![z, p.1, p.2] i) (![z, p.1, p.2] j) ∧
        adjacencyKernel W (![z, p.1, p.2] i) (![z, p.1, p.2] j) =
          (if A (![z, p.1, p.2] i) (![z, p.1, p.2] j) = true then 1 else 0) := by
    have hmp := MeasurePreserving.symm (MeasurableEquiv.finTwoArrow (α := Ω))
      (measurePreserving_finTwoArrow μ)
    have hvec (p : Ω × Ω) :
        Fin.cons z ((MeasurableEquiv.finTwoArrow (α := Ω)).symm p) =
          ![z, p.1, p.2] := by
      ext i
      fin_cases i <;> rfl
    filter_upwards [hmp.quasiMeasurePreserving.ae hzroot] with p hp
    simpa only [hvec] using hp
  filter_upwards [hpairSection, Measure.quasiMeasurePreserving_fst.ae hzrows.1,
    Measure.quasiMeasurePreserving_snd.ae hzrows.1,
    Measure.quasiMeasurePreserving_fst.ae hzrows.2,
    Measure.quasiMeasurePreserving_snd.ae hzrows.2,
    S.ae_private_cross_adjacency_one r u hW,
    hW.moment_mem,
    Measure.quasiMeasurePreserving_fst.ae R.ae_plateau_not_high,
    Measure.quasiMeasurePreserving_snd.ae R.ae_plateau_not_high]
    with p htr hA₁ hA₂ hY₁ hY₂ hxy hK hn₁ hn₂ hx hy hdiff
  have hxu : 0 < u.val p.1 := by
    have hneq : S.ρ p.1 ≠ u.val := by
      intro heq
      exact hn₁ (mem_iUnion₂.mpr ⟨u, hu, heq⟩) hx.1.1.1
    exact lt_of_not_ge (fun h => hx.2 ⟨hneq, h⟩)
  have hyu : 0 < u.val p.2 := by
    have hneq : S.ρ p.2 ≠ u.val := by
      intro heq
      exact hn₂ (mem_iUnion₂.mpr ⟨u, hu, heq⟩) hy.1.1.1
    exact lt_of_not_ge (fun h => hy.2 ⟨hneq, h⟩)
  have hxyA : A p.1 p.2 = true := by
    have heq : adjacencyKernel W p.1 p.2 =
        (if A p.1 p.2 = true then (1 : ℝ) else 0) := (htr.2 1 2 (by decide)).2
    rw [hxy hx hy hdiff] at heq
    by_contra hn
    have hf : A p.1 p.2 = false := Bool.eq_false_iff.mpr hn
    simp [hf] at heq
  have hzxA : A z p.1 = true := by
    have heq : adjacencyKernel W z p.1 =
        (if A z p.1 = true then (1 : ℝ) else 0) := (htr.2 0 1 (by decide)).2
    rw [hA₁, ite_eq_left hxu] at heq
    by_contra hn
    have hf : A z p.1 = false := Bool.eq_false_iff.mpr hn
    simp [hf] at heq
  have hzyA : A z p.2 = true := by
    have heq : adjacencyKernel W z p.2 =
        (if A z p.2 = true then (1 : ℝ) else 0) := (htr.2 0 2 (by decide)).2
    rw [hA₂, ite_eq_left hyu] at heq
    by_contra hn
    have hf : A z p.2 = false := Bool.eq_false_iff.mpr hn
    simp [hf] at heq
  have hclique : FiniteArity.TupleClique A ![z, p.1, p.2] := by
    have hxzA : A p.1 z = true := by
      simpa [A, PhysicalRepresentative.adjacency_symm] using hzxA
    have hyzA : A p.2 z = true := by
      simpa [A, PhysicalRepresentative.adjacency_symm] using hzyA
    have hyxA : A p.2 p.1 = true := by
      simpa [A, PhysicalRepresentative.adjacency_symm] using hxyA
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp <;>
      first | exact hxyA | exact hyxA | exact hzxA | exact hzyA |
        exact hxzA | exact hyzA | exact False.elim (hij rfl)
  have hbound := htr.1 hclique
  rw [tupleCharge_private_three Y z p.1 p.2
    (PhysicalRepresentative.charge_symm W m z p.1)
    (PhysicalRepresentative.charge_symm W m z p.2)
    (PhysicalRepresentative.charge_symm W m p.1 p.2)] at hbound
  have hYzx : Y z p.1 = u.val p.1 + m := by
    have heq : Y z p.1 = chargeKernel W z p.1 := by
      simpa using (htr.2 0 1 (by decide)).1
    rw [heq, hY₁, ite_eq_left hxu]
    ring
  have hYzy : Y z p.2 = u.val p.2 + m := by
    have heq : Y z p.2 = chargeKernel W z p.2 := by
      simpa using (htr.2 0 2 (by decide)).1
    rw [heq, hY₂, ite_eq_left hyu]
    ring
  have hYxy : Y p.1 p.2 = shiftedKernel W m p.1 p.2 + m := by
    have heq : Y p.1 p.2 = chargeKernel W p.1 p.2 := by
      simpa using (htr.2 1 2 (by decide)).1
    rw [heq]
    change chargeKernel W p.1 p.2 = shiftedKernel W m p.1 p.2 + m
    rw [shiftedKernel, shiftedMoment_eq]
    change chargeKernel W p.1 p.2 =
      chargeKernel W p.1 p.2 - m * adjacencyKernel W p.1 p.2 + m
    rw [hxy hx hy hdiff]
    ring
  dsimp only [twoCenterPrivateThreshold, twoCenterPrivateDeficit]
  have hrx : r.val p.1 ≤ 0 := hx.1.2.2
  have hry : r.val p.2 ≤ 0 := hy.1.2.2
  have hK0 : 0 ≤ shiftedKernel W m p.1 p.2 := hK.1
  linarith only [hbound, hYzx, hYzy, hYxy, hrx, hry, hK0]

/-- Almost every pair in the strict-low private source lies in the same
positive original whole-row class, by the actual three-clique cover. -/
theorem ReverseRecovery.ae_private_low_pair_same
    (R : S.ReverseRecovery) (r u : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hp : R.plateau = {r, u}) :
    ∀ᵐ p ∂(μ.restrict (S.twoCenterPrivateLow r u)).prod
      (μ.restrict (S.twoCenterPrivateLow r u)),
      ∃ k ∈ S.I, S.ρ p.1 = k ∧ S.ρ p.2 = k := by
  let U := S.twoCenterPrivateLow r u
  have hU : MeasurableSet U := R.measurableSet_twoCenterPrivateLow r u hp
  have hle : (μ.restrict U).prod (μ.restrict U) ≤ μ.prod μ :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  have hpair := ae_mono hle (R.ae_private_pair_deficit_cover r u hW hd hgap hp)
  have hmem : ∀ᵐ p ∂(μ.restrict U).prod (μ.restrict U), p.1 ∈ U ∧ p.2 ∈ U :=
    (Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hU)).and
      (Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hU))
  filter_upwards [hpair, hmem] with p hp hm
  by_contra hnot
  have hdiff : ∀ k ∈ S.I, S.ρ p.1 = k → S.ρ p.2 ≠ k := by
    intro k hk hx hy
    exact hnot ⟨k, hk, hx, hy⟩
  have hbound := hp hm.1.1 hm.2.1 hdiff
  have hlowx : S.twoCenterPrivateDeficit r u p.1 <
      S.twoCenterPrivateThreshold r u / 2 := hm.1.2
  have hlowy : S.twoCenterPrivateDeficit r u p.2 <
      S.twoCenterPrivateThreshold r u / 2 := hm.2.2
  linarith

/-- A positive strict-low private source concentrates in one actual
positive original whole-row fiber, even with countable atoms and dust. -/
theorem ReverseRecovery.exists_private_low_fiber
    (R : S.ReverseRecovery) (r u : S.I) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hp : R.plateau = {r, u})
    (hpos : 0 < μ (S.twoCenterPrivateLow r u)) :
    ∃ k : S.I, ∀ᵐ x ∂μ.restrict (S.twoCenterPrivateLow r u), S.ρ x = k.val := by
  obtain ⟨k, hk, hfiber⟩ := exists_fiber_of_ae_pair_same
    (S.twoCenterPrivateLow r u) hpos S.ρ S.I
    (R.ae_private_low_pair_same r u hW hd hgap hp)
  exact ⟨⟨k, hk⟩, hfiber⟩

/-- The actual private source has the fractional vertex-cover lower bound.
The atomic size input is a numerical bound on original whole-row fibers;
the old triangle test and low-set concentration are proved above. -/
theorem ReverseRecovery.private_source_deficit_integral_ge
    (R : S.ReverseRecovery) (r u : S.I) (hru : r ≠ u) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hp : R.plateau = {r, u})
    (hintercept : (1 + m) / 4 < 2 * (c - m * d) + m)
    (hdegree0 : ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)),
      (1 / 2 : ℝ) • (S.normalizedHead r + S.normalizedHead u) -
        Lp.const 2 μ (1 : ℝ)⟫ < 0)
    (hζ : 0 ≤ S.twoCenterPrivateThreshold r u) (L : ℝ)
    (hmax : ∀ k : S.I,
      μ.real (S.twoCenterPrivate r u ∩ {x | S.ρ x = k.val}) ≤ L) :
    S.twoCenterPrivateThreshold r u *
      max 0 (min (μ.real (S.twoCenterPrivate r u) / 2)
        (μ.real (S.twoCenterPrivate r u) - L)) ≤
        ∫ x in S.twoCenterPrivate r u, S.twoCenterPrivateDeficit r u x ∂μ := by
  let C := S.twoCenterPrivate r u
  let U := S.twoCenterPrivateLow r u
  let f := S.twoCenterPrivateDeficit r u
  let ζ := S.twoCenterPrivateThreshold r u
  have hC : MeasurableSet C := (R.measurableSet_twoCenter_patterns r u hp).1
  have hU : MeasurableSet U := R.measurableSet_twoCenterPrivateLow r u hp
  have hUC : U ⊆ C := inter_subset_left
  have hf : Integrable f μ := by
    have hr : Integrable (r.val : Ω → ℝ) μ := (Lp.memLp r.val).integrable (by norm_num)
    have hu : Integrable (u.val : Ω → ℝ) μ := (Lp.memLp u.val).integrable (by norm_num)
    exact ((integrable_const _).sub hr).sub hu
  have hnonneg : ∀ᵐ x ∂μ.restrict C, 0 ≤ f x := by
    simpa only [f, C, twoCenterPrivateDeficit] using
      R.ae_private_head_deficit_nonnegative r u hru hW hd hgap hp hintercept hdegree0
  by_cases hUpos : 0 < μ U
  · obtain ⟨k, hk⟩ := R.exists_private_low_fiber r u hW hd hgap hp hUpos
    let A₀ := C ∩ {x | S.ρ x = k.val}
    let A := A₀ ∪ U
    have hA₀ : MeasurableSet A₀ := hC.inter (S.hfibers k.val k.property).1
    have hA : MeasurableSet A := hA₀.union hU
    have hAC : A ⊆ C := union_subset (inter_subset_left) hUC
    have hUA : U ⊆ A := subset_union_right
    have hU_A₀ : ∀ᵐ x ∂μ, x ∈ U → x ∈ A₀ := by
      apply (ae_restrict_iff' hU).mp
      filter_upwards [hk, ae_restrict_mem hU] with x hx hmem
      exact ⟨hmem.1, hx⟩
    have hAeq : A =ᵐ[μ] A₀ := by
      filter_upwards [hU_A₀] with x hx
      apply propext
      constructor
      · intro h
        exact h.elim id (hx)
      · exact Or.inl
    have hAmass : μ.real A = μ.real A₀ :=
      congrArg ENNReal.toReal (measure_congr hAeq)
    have hAmass_le : μ.real A ≤ L := hAmass.trans_le (hmax k)
    have hnonnegU : ∀ᵐ x ∂μ.restrict U, 0 ≤ f x := by
      exact ae_mono (Measure.restrict_mono hUC le_rfl) hnonneg
    have hlow : ∀ x ∈ U, f x < ζ / 2 := fun _ hx => hx.2
    have hrest : ∀ x ∈ C \ U, ζ / 2 ≤ f x := by
      intro x hx
      exact le_of_not_gt (fun h => hx.2 ⟨hx.1, h⟩)
    have hpair : ∀ᵐ y ∂μ.restrict (C \ A),
        ∀ᵐ x ∂μ.restrict U, ζ ≤ f x + f y := by
      have hle : (μ.restrict (C \ A)).prod (μ.restrict U) ≤ μ.prod μ :=
        Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
      have hcover := ae_mono hle (R.ae_private_pair_deficit_cover r u hW hd hgap hp)
      have hmemY : ∀ᵐ p ∂(μ.restrict (C \ A)).prod (μ.restrict U), p.1 ∈ C \ A :=
        Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem (hC.diff hA))
      have hmemX : ∀ᵐ p ∂(μ.restrict (C \ A)).prod (μ.restrict U), p.2 ∈ U :=
        Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hU)
      have htagX : ∀ᵐ p ∂(μ.restrict (C \ A)).prod (μ.restrict U), S.ρ p.2 = k.val :=
        Measure.quasiMeasurePreserving_snd.ae hk
      have hprod : ∀ᵐ p ∂(μ.restrict (C \ A)).prod (μ.restrict U),
          ζ ≤ f p.2 + f p.1 := by
        filter_upwards [hcover, hmemY, hmemX, htagX]
          with p hc hy hx htag
        have hdiff : ∀ j ∈ S.I, S.ρ p.1 = j → S.ρ p.2 ≠ j := by
          intro j hj hjy hjx
          have hjk : j = k.val := hjx.symm.trans htag
          exact hy.2 (Or.inl ⟨hy.1, hjy.trans hjk⟩)
        simpa only [f, ζ, add_comm] using hc hy.1 hx.1 hdiff
      exact Measure.ae_ae_of_ae_prod hprod
    have hbound := integral_source_cover_of_low_subset C A U hA hU hAC hUA
      hUpos f hf ζ hnonnegU hlow hrest hpair
    have hA_le_C : μ.real A ≤ μ.real C := measureReal_mono hAC
    have hmin_nonneg : 0 ≤ min (μ.real C / 2) (μ.real C - μ.real A) :=
      le_min (by positivity) (sub_nonneg.mpr hA_le_C)
    have hmin_mono : min (μ.real C / 2) (μ.real C - L) ≤
        min (μ.real C / 2) (μ.real C - μ.real A) :=
      min_le_min le_rfl (sub_le_sub_left hAmass_le _)
    have hmax_le : max 0 (min (μ.real C / 2) (μ.real C - L)) ≤
        min (μ.real C / 2) (μ.real C - μ.real A) :=
      max_le hmin_nonneg hmin_mono
    exact (mul_le_mul_of_nonneg_left hmax_le hζ).trans hbound
  · have hUzero : μ U = 0 := le_antisymm (le_of_not_gt hUpos) zero_le
    have hnotU : ∀ᵐ x ∂μ, x ∉ U := measure_eq_zero_iff_ae_notMem.mp hUzero
    have hrest : ∀ᵐ x ∂μ.restrict C, ζ / 2 ≤ f x := by
      filter_upwards [ae_restrict_of_ae hnotU, ae_restrict_mem hC]
        with x hx hmem
      exact le_of_not_gt (fun h => hx ⟨hmem, h⟩)
    have hhalf : ζ * (μ.real C / 2) ≤ ∫ x in C, f x ∂μ := by
      have hi : (∫ x in C, ζ / 2 ∂μ) ≤ (∫ x in C, f x ∂μ) :=
        integral_mono_ae (integrable_const _) hf.restrict hrest
      rw [setIntegral_const] at hi
      simp only [smul_eq_mul] at hi
      nlinarith only [hi]
    have htarget : max 0 (min (μ.real C / 2) (μ.real C - L)) ≤ μ.real C / 2 :=
      max_le (by positivity) (min_le_left _ _)
    exact (mul_le_mul_of_nonneg_left htarget hζ).trans hhalf

/-- At an actual smooth E2 contact, the negative mean-head degree needed
for the private deficit is derived from the original global optimum. -/
theorem ReverseRecovery.e2_private_source_deficit_integral_ge
    (R : S.ReverseRecovery) (r u : S.I) (hru : r ≠ u) {d c q : ℝ}
    (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioc (0 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hp : R.plateau = {r, u})
    (hintercept : (1 + m) / 4 < 2 * (c - m * d) + m)
    (hζ : 0 ≤ S.twoCenterPrivateThreshold r u) (L : ℝ)
    (hmax : ∀ k : S.I,
      μ.real (S.twoCenterPrivate r u ∩ {x | S.ρ x = k.val}) ≤ L) :
    S.twoCenterPrivateThreshold r u *
      max 0 (min (μ.real (S.twoCenterPrivate r u) / 2)
        (μ.real (S.twoCenterPrivate r u) - L)) ≤
        ∫ x in S.twoCenterPrivate r u, S.twoCenterPrivateDeficit r u x ∂μ := by
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by
    rw [hdq]
    exact Benchmark.e2_density_mem hq
  exact R.private_source_deficit_integral_ge r u hru hW hd hgap hp hintercept
    (R.e2_mean_head_degree_inner_neg r u hru hW hq hdq hgap hglobal hp)
    hζ L hmax

end Erdos1017.CappedModel.SelectedHighLowStructure
