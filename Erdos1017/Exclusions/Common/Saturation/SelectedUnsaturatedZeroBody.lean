module

public import Erdos1017.Exclusions.Common.Saturation.SelectedUnsaturatedAtomDegree
public import Erdos1017.SelectedModel.MultipartiteValue.MultipartiteModelComparison
public import Erdos1017.SelectedModel.Structure.HalfGraphMultipartiteSupport
public import Erdos1017.Exclusions.Common.BoundedScalarStationarity

/-!
# Exclusion of the unsaturated zero-body branch

The zero-body branch with a universal positive cover cannot have all its atomic
stars unsaturated: with no exterior atom the support is multipartite with
singleton dust, and a sole unsaturated exterior atom is excluded whether its
missing diffuse region is null or positive.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

omit [StandardBorelSpace Ω] [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem objective_le_benchmark_of_universal_atom_blocks
    (S : SelectedHighLowStructure W m) (hfull : FullFeasible W)
    (hjoin : ∀ u : S.I, ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = u.val → S.ρ p.2 ≠ u.val →
      adjacencyKernel W p.1 p.2 = 1) : objective W ≤ benchmark (density W) := by
  let : Countable S.I := S.hI.to_subtype
  have hblocks : ∀ᵐ p ∂μ.prod μ, ∀ u : S.I,
      (S.ρ p.1 = u.val → S.ρ p.2 = u.val → adjacencyKernel W p.1 p.2 = 0) ∧
      (S.ρ p.1 = u.val → S.ρ p.2 ≠ u.val → adjacencyKernel W p.1 p.2 = 1) := by
    apply ae_all_iff.mpr
    intro u
    have hi := (S.hfibers u.val u.property).2.2.1
    rw [Measure.prod_restrict] at hi
    have hi' := (ae_restrict_iff' ((S.hfibers u.val u.property).1.prod
      (S.hfibers u.val u.property).1)).mp hi
    exact (hi'.mono (fun _ hp hx hy => hp ⟨hx, hy⟩)).and (hjoin u)
  have hD (x : Ω) (hx : S.ρ x ∉ S.I) : x ∈ S.D := by
    rw [S.hDeq]
    simp only [mem_compl_iff, mem_iUnion, mem_ofPred_eq]
    rintro ⟨u, hu, he⟩
    exact hx (he ▸ hu)
  have hsupp : ∀ᵐ p ∂μ.prod μ, adjacencyKernel W p.1 p.2 =
      if HalfGraphMultipartite.atomicDustLabel S.ρ S.I p.1 ≠
        HalfGraphMultipartite.atomicDustLabel S.ρ S.I p.2 then 1 else 0 := by
    filter_upwards [hblocks,
      (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hblocks,
      S.hDcomplete, adjacencyKernel_symm W,
      HalfGraphMultipartite.ae_coordinates_ne (μ := μ)] with p hb hbSwap hd hsym hne
    have he := HalfGraphMultipartite.atomicDustLabel_eq_iff_of_ne S.ρ S.I hne
    by_cases hs : HalfGraphMultipartite.sameAtom S.ρ S.I p.1 p.2
    · obtain ⟨u, hu, hx, hy⟩ := hs
      have heq := he.mpr ⟨u, hu, hx, hy⟩
      rw [ite_eq_right (not_not.mpr heq)]
      exact (hb ⟨u, hu⟩).1 hx hy
    · rw [ite_eq_left (fun heq => hs (he.mp heq))]
      by_cases hx : S.ρ p.1 ∈ S.I
      · exact (hb ⟨S.ρ p.1, hx⟩).2 rfl
          (fun hy => hs ⟨S.ρ p.1, hx, rfl, hy⟩)
      · by_cases hy : S.ρ p.2 ∈ S.I
        · have hneq : S.ρ p.1 ≠ S.ρ p.2 := fun heq => hx (heq.symm ▸ hy)
          exact hsym.trans ((hbSwap ⟨S.ρ p.2, hy⟩).2 rfl hneq)
        · exact hd (hD p.1 hx) (hD p.2 hy)
  apply objective_le_benchmark_of_partition_support W hfull
    (HalfGraphMultipartite.atomicDustLabel S.ρ S.I)
  filter_upwards [hsupp] with p hp
  by_cases hne : HalfGraphMultipartite.atomicDustLabel S.ρ S.I p.1 ≠
      HalfGraphMultipartite.atomicDustLabel S.ρ S.I p.2
  · rw [ite_eq_left hne] at hp
    filter_upwards [ae_adjacency_one_of_moment_one W p hp] with z hz
    exact ⟨fun _ => hne, fun _ => hz⟩
  · rw [ite_eq_right hne] at hp
    filter_upwards [ae_adjacency_zero_of_moment_zero W p hp] with z hz
    exact iff_of_false (by simp [hz]) hne

/-- With no exterior original atom, the actual zero-body support is
multipartite with genuine singleton dust, contradicting its strict gap. -/
theorem not_zero_body_only_root (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) (hatoms : ∀ u : S.I, u = r) : False := by
  have hN := S.root_neutral_of_zero_body r hW hd hgap hzero
  have hjoin : ∀ u : S.I, ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = u.val → S.ρ p.2 ≠ u.val →
      adjacencyKernel W p.1 p.2 = 1 := by
    intro u
    rw [hatoms u]
    filter_upwards [S.neutral_atom_adjacency r hW hd hgap hN] with p hp hx hy
    exact (hp hx).trans (ite_eq_right hy)
  have hb := objective_le_benchmark_of_universal_atom_blocks S hW.full hjoin
  rw [hW.objective_eq, hW.density_eq] at hb
  exact (not_le_of_gt hgap) hb

/-- If the sole exterior atom misses a null part of the genuine diffuse
remainder, every original independent class is universal and the actual
support is multipartite. -/
theorem not_zero_body_two_atoms_of_null_missing
    (S : SelectedHighLowStructure W m) (r u : S.I) (hru : r ≠ u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hatoms : ∀ v : S.I, v = r ∨ v = u)
    (hP : μ (S.D \ S.rootNeighborhood u) = 0) : False := by
  have hN := S.root_neutral_of_zero_body r hW hd hgap hzero
  have hroot := S.neutral_atom_adjacency r hW hd hgap hN
  have hrootSwap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hroot
  have hjoin : ∀ v : S.I, ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = v.val → S.ρ p.2 ≠ v.val →
      adjacencyKernel W p.1 p.2 = 1 := by
    intro v
    rcases hatoms v with hv | hv
    · rw [hv]
      filter_upwards [hroot] with p hp hx hy
      exact (hp hx).trans (ite_eq_right hy)
    · rw [hv]
      filter_upwards [S.ae_original_root_adjacency u hW hd hgap, hrootSwap, adjacencyKernel_symm W,
        Measure.quasiMeasurePreserving_snd.ae (measure_eq_zero_iff_ae_notMem.mp hP)]
        with p hp hr hsym hP hx hy
      by_cases hyr : S.ρ p.2 = r.val
      · have hxr : S.ρ p.1 ≠ r.val := fun he => hru (Subtype.ext (he.symm.trans hx))
        have hG := hr hyr
        exact hsym.trans (hG.trans (ite_eq_right hxr))
      · have hyD : p.2 ∈ S.D := by
          rw [S.hDeq]
          simp only [mem_compl_iff, mem_iUnion, mem_ofPred_eq]
          rintro ⟨v, hv, he⟩
          rcases hatoms ⟨v, hv⟩ with hv | hv
          · exact hyr (he.trans (congrArg Subtype.val hv))
          · exact hy (he.trans (congrArg Subtype.val hv))
        have hyN : p.2 ∈ S.rootNeighborhood u := by
          by_contra hn
          exact hP ⟨hyD, hn⟩
        exact (hp hx).trans (ite_eq_left hyN)
  have hb := objective_le_benchmark_of_universal_atom_blocks S hW.full hjoin
  rw [hW.objective_eq, hW.density_eq] at hb
  exact (not_le_of_gt hgap) hb

/-- A sole unsaturated exterior atom cannot retain a positive missing
diffuse region. The objective-preserving signed competitor receives its
own scalar stationary rows on the same graph before its multiplier is compared. -/
theorem not_zero_body_two_atoms_of_positive_missing
    (S : SelectedHighLowStructure W m) (r u : S.I) (hru : r ≠ u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : 1 / 2 < -m)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hratio : μ.real {x | S.ρ x = r.val} * (1 + m) < 2 * (2 * (c - m * d) + m))
    (hnot : ¬S.IsSaturatedAtomPair r u) (hatoms : ∀ v : S.I, v = r ∨ v = u)
    (hPpos : 0 < μ (S.D \ S.rootNeighborhood u)) : False := by
  let A := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  let I := {x | S.ρ x = r.val}
  let J := {x | S.ρ x = u.val}
  let P := S.D \ S.rootNeighborhood u
  let G := fun x y => if A x y = true then (1 : ℝ) else 0
  let t := S.coveredCountableBoundaryCoefficient (Sum.inl r) (Sum.inl u)
  let eps := IndependentStarPerturbation.radius t ((1 + m) / 2) / 2
  let Z := IndependentStarPerturbation.charge A Y I J eps
  have hI : MeasurableSet I := (S.hfibers r.val r.property).1
  have hJ : MeasurableSet J := (S.hfibers u.val u.property).1
  have hP : MeasurableSet P := S.hD.diff (S.measurableSet_rootNeighborhood u)
  have hdisj : Disjoint I J := Set.disjoint_left.mpr
    (fun x hx hy => hru (Subtype.ext (hx.symm.trans hy)))
  have hDchar (x : Ω) : x ∈ S.D ↔ S.ρ x ≠ r.val ∧ S.ρ x ≠ u.val := by
    rw [S.hDeq]
    simp only [mem_compl_iff, mem_iUnion, mem_ofPred_eq]
    constructor
    · intro hx
      exact ⟨fun hr => hx ⟨r.val, r.property, hr⟩, fun hu => hx ⟨u.val, u.property, hu⟩⟩
    · rintro ⟨hr, hu⟩ ⟨v, hv, he⟩
      rcases hatoms ⟨v, hv⟩ with hv | hv
      · exact hr (he.trans (congrArg Subtype.val hv))
      · exact hu (he.trans (congrArg Subtype.val hv))
  have hs := hW.strict_gap_structure hd hgap
  obtain ⟨ht, hp⟩ := S.unsaturated_atom_star_margin r u hru hW hd hgap hell hzero hratio hnot
  have hrad : 0 < IndependentStarPerturbation.radius t ((1 + m) / 2) :=
    IndependentStarPerturbation.radius_pos (by dsimp [t]; linarith) hp
  have heps : 0 < eps := half_pos hrad
  have hepsB : |eps| ≤ IndependentStarPerturbation.radius t ((1 + m) / 2) := by
    rw [abs_of_pos heps]
    dsimp [eps]
    linarith
  have hfull := S.unsaturated_atom_star_full_tests r u hru hW hd hgap hell hzero hratio hnot eps hepsB
  have hA := PhysicalRepresentative.measurable_adjacency W m
  have hY := PhysicalRepresentative.measurable_charge W m
  have hZ : Measurable (Function.uncurry Z) :=
    IndependentStarPerturbation.measurable_charge A hA Y hY I J hI hJ eps
  have hZbound (p : Ω × Ω) : ‖Z p.1 p.2‖ ≤ 3 + |eps| := by
    rw [Real.norm_eq_abs]
    exact IndependentStarPerturbation.charge_abs_bound A Y I J eps 3
      (PhysicalRepresentative.charge_bound W m) p.1 p.2
  have hYint : Integrable (Function.uncurry Y) (μ.prod μ) := Integrable.of_bound
    hY.aestronglyMeasurable 3 (Eventually.of_forall (fun p => by
      change ‖Y p.1 p.2‖ ≤ 3
      rw [Real.norm_eq_abs]
      exact PhysicalRepresentative.charge_bound W m p.1 p.2))
  have hsection := S.ae_atom_outside_neighbor_mass r u hW hd hgap
  have hbalance := S.unsaturated_atom_outside_mass_eq r u hru hW hd hgap hell hzero hratio hnot
  have hcost : FiniteCappedSamplingCost.physicalObjective μ Z = c := by
    rw [IndependentStarPerturbation.physicalObjective_charge_of_constant_outside A hA
      (PhysicalRepresentative.adjacency_symm W m) Y hYint I J hI hJ hdisj eps _ hsection,
      hbalance, sub_self, mul_zero, add_zero]
    exact (PhysicalRepresentative.objective_eq W m hs.strict_support).trans hW.objective_eq
  have hdensity : FiniteCappedSamplingCost.physicalDensity μ A = d :=
    (PhysicalRepresentative.density_eq W m hs.strict_support).trans hW.density_eq
  have hopt : FiniteCappedSamplingCost.physicalObjective μ Z =
      FractionalGraph.densityLimit (FiniteCappedSamplingCost.physicalDensity μ A) := by
    rw [hcost, hdensity]
    exact hW.optimal
  have hGeq : ∀ᵐ p ∂μ.prod μ, adjacencyKernel W p.1 p.2 = G p.1 p.2 :=
    PhysicalRepresentative.adjacency_moment_ae_eq W m hs.strict_support
  have hGmeas : AEStronglyMeasurable (Function.uncurry G) (μ.prod μ) :=
    (Measurable.ite (hA (measurableSet_singleton true)) measurable_const measurable_const).aestronglyMeasurable
  have hGbound : ∀ᵐ p ∂μ.prod μ, ‖G p.1 p.2‖ ≤ 1 := Eventually.of_forall (fun p => by
    dsimp [G]
    split_ifs <;> norm_num)
  have hregular : Variation.weightFirstVariation
      (KernelOperator.operator G (by norm_num : (0 : ℝ) ≤ 1) hGmeas hGbound) ≠ 0 := by
    intro hz
    obtain ⟨a, ha⟩ := (Variation.kernel_weightFirstVariation_eq_zero_iff G (by norm_num)
      hGmeas hGbound).mp hz
    apply hs.nonconstant_degree
    refine ⟨a, ?_⟩
    filter_upwards [ha, Measure.ae_ae_of_ae_prod hGeq] with x hx he
    exact (integral_congr_ae he).trans hx
  have hjoined : ∀ᵐ p ∂μ.prod μ,
      (p.1 ∈ I ∧ p.2 ∈ J) ∨ (p.2 ∈ I ∧ p.1 ∈ J) → A p.1 p.2 = true := by
    have hu := S.ae_root_universal_of_zero_body r hW hd hgap hzero
    filter_upwards [hu,
      (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hu]
      with p hp hq h
    rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact (hp hx).mpr (fun he => hru (Subtype.ext (he.symm.trans hy)))
    · exact (PhysicalRepresentative.adjacency_symm W m _ _).trans
        ((hq hx).mpr (fun he => hru (Subtype.ext (he.symm.trans hy))))
  have hZzero := IndependentStarPerturbation.charge_zero_ae μ A Y I J eps
    (Eventually.of_forall (fun p => PhysicalRepresentative.charge_zero_of_nonedge W m _ _)) hjoined
  obtain ⟨n, nu, _, _, _, _, hnew, _, _⟩ :=
    FiniteCappedSamplingCost.exists_stationary_shift_of_bounded_full_scalar_optimum
      A (PhysicalRepresentative.adjacency_symm W m) hA Z hZ (3 + |eps|) (by positivity) hZbound
      (Eventually.of_forall (fun p => IndependentStarPerturbation.charge_symm A Y
        (PhysicalRepresentative.adjacency_symm W m) (PhysicalRepresentative.charge_symm W m)
        I J eps p.1 p.2)) hZzero hfull hopt G (fun _ _ => rfl) hGmeas hGbound hregular
  have hYrow (x : Ω) : Integrable (Y x) μ := Integrable.of_bound
    ((hY.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable) 3
    (Eventually.of_forall (fun y => by rw [Real.norm_eq_abs]; exact PhysicalRepresentative.charge_bound W m x y))
  have hGrow (x : Ω) : Integrable (G x) μ := Integrable.of_bound
    ((Measurable.ite (hA (measurableSet_singleton true)) measurable_const measurable_const).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
    (Eventually.of_forall (fun y => by dsimp [G]; split_ifs <;> norm_num))
  have hZrow (x : Ω) : Integrable (Z x) μ := Integrable.of_bound
    ((hZ.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable) (3 + |eps|)
    (Eventually.of_forall (fun y => hZbound (x, y)))
  have hold : ∀ᵐ x ∂μ, (∫ y, Y x y - m * G x y ∂μ) = 2 * (c - m * d) := by
    filter_upwards [hW.stationary, Measure.ae_ae_of_ae_prod
      ((PhysicalRepresentative.charge_ae_eq W m hs.strict_support).and hGeq)] with x hx he
    apply Eq.trans _ hx
    apply integral_congr_ae
    filter_upwards [he] with y hy
    change Y x y - m * G x y = shiftedMoment W m (x, y)
    rw [shiftedMoment_eq]
    exact congrArg₂ (fun a b => a - m * b) hy.1 hy.2.symm
  have hrows : ∀ᵐ x ∂μ, nu = 2 * (c - m * d) +
      eps * (∫ y, IndependentStarPerturbation.direction A I J x y ∂μ) +
        (m - n) * (∫ y, G x y ∂μ) := by
    filter_upwards [hnew, hold] with x hn hm
    rw [integral_sub (hZrow x) ((hGrow x).const_mul n),
      IndependentStarPerturbation.integral_charge_row A hA Y I J hI hJ eps x (hYrow x),
      integral_const_mul] at hn
    rw [integral_sub (hYrow x) ((hGrow x).const_mul m), integral_const_mul] at hm
    linarith
  have hRmass : μ.real (S.D ∩ S.rootNeighborhood u) = μ.real I := by
    have he : S.rootNeighborhood u \ I = S.D ∩ S.rootNeighborhood u := by
      ext x
      change (x ∈ S.rootNeighborhood u ∧ x ∉ I) ↔ x ∈ S.D ∧ x ∈ S.rootNeighborhood u
      rw [hDchar]
      change (S.ρ x ≠ u.val ∧ 0 < u.val x) ∧ S.ρ x ≠ r.val ↔
        (S.ρ x ≠ r.val ∧ S.ρ x ≠ u.val) ∧ (S.ρ x ≠ u.val ∧ 0 < u.val x)
      tauto
    rw [he] at hbalance
    exact hbalance
  have hmass : 1 - μ.real J = 2 * μ.real I + μ.real P := by
    have he : I ∪ J = S.Dᶜ := by
      ext x
      rw [mem_compl_iff, hDchar]
      change (S.ρ x = r.val ∨ S.ρ x = u.val) ↔ ¬(S.ρ x ≠ r.val ∧ S.ρ x ≠ u.val)
      tauto
    have hi := measureReal_union (μ := μ) hdisj hJ
    rw [he, measureReal_compl S.hD, probReal_univ] at hi
    have hd := measureReal_inter_add_sdiff (μ := μ) (s := S.D) (S.measurableSet_rootNeighborhood u)
    rw [hRmass] at hd
    change μ.real I + μ.real P = μ.real S.D at hd
    linarith
  have hdegJ : ∀ᵐ x ∂μ, x ∈ J → (∫ y, G x y ∂μ) = 2 * μ.real I := by
    filter_upwards [Measure.ae_ae_of_ae_prod (S.ae_root_adjacency u hW hd hgap)] with x hx hu
    have he : G x =ᵐ[μ] (S.rootNeighborhood u).indicator (fun _ => (1 : ℝ)) := by
      filter_upwards [hx] with y hy
      change (if A x y = true then (1 : ℝ) else 0) = _
      by_cases hn : y ∈ S.rootNeighborhood u
      · have ha : A x y = true := (hy hu).mpr hn
        simp [ha, hn]
      · have ha : ¬A x y = true := fun h => hn ((hy hu).mp h)
        simp [ha, hn]
    rw [integral_congr_ae he, integral_indicator (S.measurableSet_rootNeighborhood u), setIntegral_const]
    simpa using S.unsaturated_atom_neighborhood_mass_eq_twice r u hru hW hd hgap hell hzero hratio hnot
  have hdirJ : ∀ᵐ x ∂μ, x ∈ J → (∫ y, IndependentStarPerturbation.direction A I J x y ∂μ) = 0 := by
    filter_upwards [hsection] with x hx hu
    rw [IndependentStarPerturbation.integral_direction_row_cell A hA I J hI hJ hdisj x hu,
      hx hu, hbalance, sub_self]
  have houtside : ∀ᵐ p ∂μ.prod μ, p.1 ∈ P →
      G p.1 p.2 = if p.2 ∈ J then 0 else 1 := by
    have hroot := S.ae_root_universal_of_zero_body r hW hd hgap hzero
    filter_upwards [(Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
        (S.ae_root_adjacency u hW hd hgap),
      (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hroot,
      S.hDcomplete, PhysicalRepresentative.adjacency_moment_ae_eq W m hs.strict_support]
      with p hj hr hd hp hx
    have hxD : p.1 ∈ S.D := hx.1
    have hxI := (hDchar p.1).mp hxD
    by_cases hy : p.2 ∈ J
    · have hn : A p.2 p.1 ≠ true := fun ha => hx.2 ((hj hy).mp ha)
      have ha : A p.1 p.2 = false :=
        (PhysicalRepresentative.adjacency_symm W m _ _).trans (Bool.eq_false_iff.mpr hn)
      simp [G, ha, hy]
    · by_cases hyI : p.2 ∈ I
      · have ha : A p.1 p.2 = true := (PhysicalRepresentative.adjacency_symm W m _ _).trans
          ((hr hyI).mpr hxI.1)
        simp [G, ha, hy]
      · have hyD := (hDchar p.2).mpr ⟨hyI, hy⟩
        have hG := hd hxD hyD
        change W.moment CappedColor.adjacency p = 1 at hG
        have he : G p.1 p.2 = 1 := hp.symm.trans hG
        simpa only [hy, ite_false] using he
  have hdegP : ∀ᵐ x ∂μ, x ∈ P → (∫ y, G x y ∂μ) = 1 - μ.real J := by
    filter_upwards [Measure.ae_ae_of_ae_prod houtside] with x hx hp
    have he : G x =ᵐ[μ] Jᶜ.indicator (fun _ => (1 : ℝ)) := by
      filter_upwards [hx] with y hy
      rw [hy hp]
      by_cases hyJ : y ∈ J <;> simp [hyJ]
    rw [integral_congr_ae he, integral_indicator hJ.compl, setIntegral_const]
    simp [measureReal_compl hJ]
  have hdirP : ∀ᵐ x ∂μ, x ∈ P → (∫ y, IndependentStarPerturbation.direction A I J x y ∂μ) = 0 := by
    filter_upwards [Measure.ae_ae_of_ae_prod houtside] with x hx hp
    obtain ⟨hxI, hxJ⟩ := (hDchar x).mp hp.1
    rw [IndependentStarPerturbation.integral_direction_row_outside A hA I J hJ x hxI hxJ]
    have hnull : μ (J ∩ {y | A x y = true}) = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [hx] with y hy hm
      have hg := hy hp
      simp only [hm.1, ite_true] at hg
      change (if A x y = true then (1 : ℝ) else 0) = 0 at hg
      rw [ite_eq_left (show A x y = true from hm.2)] at hg
      norm_num at hg
    simp [Measure.real, hnull]
  have hjointJ : ∀ᵐ x ∂μ.restrict J,
      nu = 2 * (c - m * d) + eps * (∫ y, IndependentStarPerturbation.direction A I J x y ∂μ) +
        (m - n) * (∫ y, G x y ∂μ) ∧
      (∫ y, G x y ∂μ) = 2 * μ.real I ∧
      (∫ y, IndependentStarPerturbation.direction A I J x y ∂μ) = 0 := by
    filter_upwards [ae_restrict_of_ae hrows, ae_restrict_of_ae hdegJ,
      ae_restrict_of_ae hdirJ, ae_restrict_mem hJ] with x hr hg hd hx
    exact ⟨hr, hg hx, hd hx⟩
  have hjointP : ∀ᵐ x ∂μ.restrict P,
      nu = 2 * (c - m * d) + eps * (∫ y, IndependentStarPerturbation.direction A I J x y ∂μ) +
        (m - n) * (∫ y, G x y ∂μ) ∧
      (∫ y, G x y ∂μ) = 1 - μ.real J ∧
      (∫ y, IndependentStarPerturbation.direction A I J x y ∂μ) = 0 := by
    filter_upwards [ae_restrict_of_ae hrows, ae_restrict_of_ae hdegP,
      ae_restrict_of_ae hdirP, ae_restrict_mem hP] with x hr hg hd hx
    exact ⟨hr, hg hx, hd hx⟩
  obtain ⟨x, _, hxr, hxg, hxd⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers u.val u.property).2.1.ne' hjointJ
  obtain ⟨y, _, hyr, hyg, hyd⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hPpos.ne' hjointP
  rw [hxg, hxd] at hxr
  rw [hyg, hyd] at hyr
  have hPmass : 0 < μ.real P := ENNReal.toReal_pos hPpos.ne' (measure_ne_top _ _)
  have hdiff : 0 < (1 - μ.real J) - 2 * μ.real I := by linarith
  have hmul : (m - n) * ((1 - μ.real J) - 2 * μ.real I) = 0 := by nlinarith only [hxr, hyr]
  have hmn : m = n := sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hdiff.ne')
  have hnu : nu = 2 * (c - m * d) := by rw [← hmn] at hxr; simpa using hxr
  obtain ⟨z, hz, hzr⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers r.val r.property).2.1.ne' (ae_restrict_of_ae hrows)
  rw [IndependentStarPerturbation.integral_direction_row_root A I J hJ hdisj z hz,
    ← hmn, sub_self, zero_mul, add_zero, hnu] at hzr
  have hJmass : 0 < μ.real J := ENNReal.toReal_pos (S.hfibers u.val u.property).2.1.ne' (measure_ne_top _ _)
  nlinarith [mul_pos heps hJmass]

/-- The actual universal positive-cover zero-body branch cannot have all
its original atomic stars unsaturated. Every finite witness, signed edit,
degree identity, atom exhaustion and edited own multiplier is derived. -/
theorem not_zero_body_of_no_saturated_partner
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : 1 / 2 < -m)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hratio : μ.real {x | S.ρ x = r.val} * (1 + m) < 2 * (2 * (c - m * d) + m))
    (hnosat : ∀ u : S.I, u ≠ r → ¬S.IsSaturatedAtomPair r u) : False := by
  by_cases hex : ∃ u : S.I, u ≠ r
  · obtain ⟨u, hur⟩ := hex
    have hru := Ne.symm hur
    have hnot := hnosat u hur
    have hatoms : ∀ v : S.I, v = r ∨ v = u := by
      intro v
      by_cases hvr : v = r
      · exact Or.inl hvr
      · exact Or.inr (S.unsaturated_exterior_atom_unique r v u (Ne.symm hvr) hru
          hW hd hgap hell hzero hratio (hnosat v hvr) hnot)
    by_cases hP : μ (S.D \ S.rootNeighborhood u) = 0
    · exact S.not_zero_body_two_atoms_of_null_missing r u hru hW hd hgap hzero hatoms hP
    · exact S.not_zero_body_two_atoms_of_positive_missing r u hru hW hd hgap hell hzero hratio
        hnot hatoms (pos_iff_ne_zero.mpr hP)
  · exact S.not_zero_body_only_root r hW hd hgap hzero
      (fun u => by by_contra hur; exact hex ⟨u, hur⟩)

end Erdos1017.CappedModel.SelectedHighLowStructure
