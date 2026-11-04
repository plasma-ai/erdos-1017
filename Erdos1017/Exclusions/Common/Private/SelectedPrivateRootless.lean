module

public import Erdos1017.Exclusions.Common.Private.SelectedPrivatePositiveStars

/-!
# Half-quota objective bound for the private model

Every positive-order private parent has a root in one of the two fibers,
unsaturation removes the order-two private law, and the two exact root quotas
pay twice the private primal cost, giving the unsaturated half-quota objective
bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

private theorem measurableSet_no_root {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (I : Set Ω) (hI : MeasurableSet I) :
    MeasurableSet {v : Fin n → Ω | ∀ i, v i ∉ I} := by
  have h := MeasurableSet.iInter (fun i : Fin n => (hI.preimage (measurable_pi_apply i)).compl)
  convert h using 1
  ext v
  simp

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m} {r p : S.I} {c : ℝ}

namespace PrivatePhysicalPrimal

private theorem ae_rootChargeRow_lt_one_of_unsaturated
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1)
    (hunsat : ∀ u : S.I, r ≠ u → ¬S.IsSaturatedAtomPair r u) :
    ∀ᵐ y ∂μ, S.rootChargeRow r y < 1 := by
  let : Countable S.I := S.hI.to_subtype
  let Ir := {x | S.ρ x = r.val}
  have hIr := S.hfibers r.val r.property
  have hatom : ∀ᵐ y ∂μ, ∀ u : S.I, S.ρ y = u.val → S.rootChargeRow r y < 1 := by
    apply ae_all_iff.mpr
    intro u
    by_cases hru : r = u
    · subst u
      filter_upwards [S.rootChargeRow_zero_off_neighborhood r hW hd hgap] with y hy hyr
      have hn : y ∉ S.rootNeighborhood r :=
        Set.disjoint_left.mp (S.rootNeighborhood_disjoint r) hyr
      rw [hy hn]
      norm_num
    · exact (ae_restrict_iff' (S.hfibers u.val u.property).1).mp
        (S.ae_rootChargeRow_lt_one_of_not_saturated r u hru hW hd hgap (hunsat u hru))
  have hdiff : ∀ᵐ y ∂μ, y ∈ S.D → S.rootChargeRow r y < 1 := by
    have hp : ∀ᵐ p ∂μ.prod μ, p.1 ∈ Ir → p.2 ∈ S.D → S.rootChargeRow r p.2 < 1 := by
      filter_upwards [S.ae_root_charge r hW hd hgap,
        PhysicalRepresentative.charge_ae_eq W m
          (hW.strict_gap_structure hd hgap).strict_support,
        S.charge_lt_one_on_atom_diffuse hW hd hgap hell r] with p hr he hc hx hy
      rw [← hr hx, he]
      exact hc hx hy
    obtain ⟨x, hx, hrow⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      hIr.2.1.ne' ((ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hp)).and
        (ae_restrict_mem hIr.1))
    exact hrow.1.mono (fun _ hy hD => hy hrow.2 hD)
  filter_upwards [hatom, hdiff] with y ha hD
  by_cases hyD : y ∈ S.D
  · exact hD hyD
  · have hu : y ∈ ⋃ u ∈ S.I, {x | S.ρ x = u} := by
      simpa only [S.hDeq, mem_compl_iff, not_not] using hyD
    obtain ⟨u, hyu⟩ := mem_iUnion.mp hu
    obtain ⟨huI, hyu⟩ := mem_iUnion.mp hyu
    exact ha ⟨u, huI⟩ hyu

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem ae_pairs
    {S : SelectedHighLowStructure W m} {r u : S.I} {c : ℝ}
    (P : S.PrivatePhysicalPrimal r u c)
    (F : Ω × Ω → Prop) (hF : ∀ᵐ p ∂μ.prod μ, F p) (n : ℕ) :
    ∀ᵐ v ∂P.laws n, ∀ i j, i ≠ j → F (v i, v j) := by
  apply PhysicalPrimal.ae_all_pairs_of_balance P.laws _ P.feasible.2.2.2 F _ n
  exact Measure.absolutelyContinuous_restrict.ae_le hF

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem ae_vertices
    {S : SelectedHighLowStructure W m} {r u : S.I} {c : ℝ}
    (P : S.PrivatePhysicalPrimal r u c)
    (F : Ω → Prop) (hF : ∀ᵐ x ∂μ, F x) (n : ℕ) :
    ∀ᵐ v ∂P.laws n, ∀ i, F (v i) := by
  simp only [ae_all_iff]
  intro i
  have hc := PhysicalPrimal.coordinate_marginal_absolutelyContinuous_of_balance
    P.laws _ P.feasible.1 P.feasible.2.1 P.feasible.2.2.2 n i
  have hd := (PhysicalPrimal.graphDemand_fst_le μ
    {p | PhysicalRepresentative.adjacency W m p.1 p.2 = true}).absolutelyContinuous
  exact ae_of_ae_map (measurable_pi_apply i).aemeasurable ((hc.trans hd).ae_le hF)

omit [StandardBorelSpace Ω] [MeasurableEq Ω] in
private theorem orderRootLeaves_eq_zero_of_no_incidence
    {n : ℕ} (ρ : Measure (Fin n → Ω)) (I B : Set Ω) (hB : MeasurableSet B)
    (hno : ∀ᵐ v ∂ρ, ∀ i j, i ≠ j → v i ∈ I → v j ∈ B → False) :
    PhysicalPrimal.orderRootLeaves n ρ I B = 0 := by
  rw [PhysicalPrimal.orderRootLeaves, Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro ij _
  rw [Measure.map_apply (measurable_pi_apply _) hB,
    Measure.restrict_apply (hB.preimage (measurable_pi_apply _))]
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [hno] with v hv hm
  exact hv ij.val.1 ij.val.2 ij.property hm.2 hm.1

/-- Unsaturation excludes all order-two incidence rooted at the second original fiber. -/
theorem orderRootLeaves_two_second_eq_zero
    {d : ℝ} (P : S.PrivatePhysicalPrimal r p c)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1)
    (hunsat : ∀ u : S.I, p ≠ u → ¬S.IsSaturatedAtomPair p u) :
    PhysicalPrimal.orderRootLeaves 2 (P.laws 2) {x | S.ρ x = p.val} = 0 := by
  have hslack := ae_vertices P _
    (ae_rootChargeRow_lt_one_of_unsaturated S p hW hd hgap hell hunsat) 2
  have hrow := ae_pairs P _ (S.ae_root_charge p hW hd hgap) 2
  apply Measure.ext
  intro B hB
  apply orderRootLeaves_eq_zero_of_no_incidence (P.laws 2) _ B hB
  filter_upwards [hslack, hrow, P.tight_physical 2]
    with v hs hr ht i j hij hi _
  have hcharge : PhysicalPrimal.charge
      (Function.uncurry (PhysicalRepresentative.charge W m)) v =
      PhysicalRepresentative.charge W m (v 0) (v 1) := by
    rw [MultipartiteHeadPrice.physicalCharge_eq_tupleCharge]
    simp [FiniteArity.tupleCharge, FiniteArity.pairCharge, FiniteArity.crossSum,
      Fin.sum_univ_succ, PhysicalRepresentative.charge_symm W m (v 1) (v 0)]
  have hpair : ∀ a b : Fin 2, a ≠ b →
      PhysicalRepresentative.charge W m (v a) (v b) = 1 := by
    intro a b hab
    fin_cases a <;> fin_cases b
    · exact False.elim (hab rfl)
    · exact hcharge.symm.trans ht
    · exact (PhysicalRepresentative.charge_symm W m (v 1) (v 0)).trans
        (hcharge.symm.trans ht)
    · exact False.elim (hab rfl)
  have hlt := hs j
  have he := hr i j hij hi
  linarith [hpair i j hij]

private theorem ae_private_second_root_off_first_local
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

private theorem private_neighbor_mass
    (S : SelectedHighLowStructure W m) (i p : S.I) (hip : i ≠ p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hprivate : ∀ᵐ q ∂μ.prod μ, S.ρ q.1 = i.val →
      adjacencyKernel W q.1 q.2 =
        if S.ρ q.2 = i.val ∨ S.ρ q.2 = p.val then 0 else 1) :
    μ.real (S.rootNeighborhood p) =
      1 - μ.real {x | S.ρ x = i.val} - μ.real {x | S.ρ x = p.val} -
        μ.real (({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ \ S.rootNeighborhood p) := by
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
  have hNpI := ae_private_second_root_off_first_local S i p hW hd hgap hprivate
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
  exact hNreal

/-- Inserting a fresh first-root point into a hypothetical rootless parent
strictly increases its tight physical charge. Pair balance licenses all
original sampled constraints for the singular parent law. -/
theorem noRootLaw_eq_zero (P : S.PrivatePhysicalPrimal r p c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpeak : S.IsCommonForwardPeak d c r)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.H)
    (hprivate : ∀ᵐ q ∂μ.prod μ, S.ρ q.1 = r.val →
      adjacencyKernel W q.1 q.2 =
        if S.ρ q.2 = r.val ∨ S.ρ q.2 = p.val then 0 else 1)
    (hA : 1 / 3 < μ.real {x | S.ρ x = r.val})
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * (1 + m) * μ.real {x | S.ρ x = r.val} <
      3 * (2 * (c - m * d) + m))
    (n : ℕ) : PhysicalRootReplacement.noRootLaw (P.laws n)
      ({x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val}) = 0 := by
  classical
  by_cases hn : 2 ≤ n
  · have : IsFiniteMeasure (P.laws n) := P.finite n
    let I := ({x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val})
    have hI : MeasurableSet I :=
      (S.hfibers r.val r.property).1.union (S.hfibers p.val p.property).1
    let ρ := PhysicalRootReplacement.noRootLaw (P.laws n) I
    have : IsFiniteMeasure ρ := by dsimp [ρ]; infer_instance
    let ν : Measure Ω := PhysicalRootReplacement.rootLaw μ {x | S.ρ x = r.val}
      (S.hfibers r.val r.property).2.1.ne'
    have : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
    have hν : ν ≪ μ := PhysicalCliqueRepresentative.cellLaw_absolutelyContinuous μ {x | S.ρ x = r.val}
    have hνI : ∀ᵐ z ∂ν, S.ρ z = r.val := by
      change ∀ᵐ z ∂(μ {x | S.ρ x = r.val})⁻¹ • μ.restrict {x | S.ρ x = r.val},
        S.ρ z = r.val
      exact Measure.ae_smul_measure (ae_restrict_mem (S.hfibers r.val r.property).1) _
    have hρ : ρ ≪ P.laws n := Measure.absolutelyContinuous_restrict
    have hdemand : PhysicalPrimal.graphDemand μ
        {p | PhysicalRepresentative.adjacency W m p.1 p.2 = true} ≪ μ.prod μ :=
      Measure.absolutelyContinuous_restrict
    have hpairs : ∀ i j : Fin n, i ≠ j → ρ.map (fun v => (v i, v j)) ≪ μ.prod μ := by
      intro i j hij
      exact (hρ.map ((measurable_pi_apply i).prodMk (measurable_pi_apply j))).trans
        ((PhysicalPrimal.pair_marginal_absolutelyContinuous_of_balance P.laws _
          P.feasible.2.2.2 n ⟨(i, j), hij⟩).trans hdemand)
    let G := Function.uncurry (PhysicalRepresentative.adjacency W m)
    let Y := Function.uncurry (PhysicalRepresentative.charge W m)
    have hs := hW.strict_gap_structure hd hgap
    have htest : ∀ k, 2 ≤ k → ∀ᵐ v ∂Measure.pi (fun _ : Fin k => μ),
        PhysicalCliqueRepresentative.Clique G v → PhysicalPrimal.charge Y v ≤ 1 := by
      intro k _
      filter_upwards [PhysicalRepresentative.full_feasible W hW.full m hs.strict_support
        hW.deterministic k] with v hv hc
      change PhysicalPrimal.charge (Function.uncurry (PhysicalRepresentative.charge W m)) v ≤ 1
      rw [MultipartiteHeadPrice.physicalCharge_eq_tupleCharge]
      exact hv hc
    have hfresh := PhysicalCliqueRepresentative.freshLaw_pairs_absolutelyContinuous μ hn
      ρ hpairs ν hν
    have hlicense := PhysicalCliqueRepresentative.ae_charge_le_of_pair_marginals μ
      (PhysicalRepresentative.measurable_adjacency W m) (PhysicalRepresentative.measurable_charge W m)
      3 (by norm_num) (fun p => PhysicalRepresentative.charge_bound W m p.1 p.2)
      htest (PhysicalCliqueRepresentative.freshLaw ν ρ) hfresh
    have hlicenseProd := ae_of_ae_map PhysicalCliqueRepresentative.measurable_cons.aemeasurable hlicense
    have hrow : ∀ᵐ z ∂μ.prod μ,
        (S.ρ z.1 = r.val → (G z = true ↔ z.2 ∉ I)) ∧
        (S.ρ z.1 = r.val → Y z = S.rootChargeRow r z.2) := by
      filter_upwards [S.ae_root_adjacency r hW hd hgap,
        Measure.quasiMeasurePreserving_snd.ae
          (S.ae_private_rootNeighborhood_iff r p hW hd hgap hprivate),
        S.ae_root_charge r hW hd hgap] with z ha hn hc
      constructor
      · intro hi
        exact (ha hi).trans (by simpa only [I, Set.mem_union, Set.mem_ofPred_eq,
          not_or] using hn)
      · exact hc
    have hfacts : ∀ᵐ w ∂PhysicalCliqueRepresentative.freshLaw ν ρ,
        ∀ i j : Fin (n + 1), i ≠ j →
          (S.ρ (w i) = r.val → (G (w i, w j) = true ↔ w j ∉ I)) ∧
          (S.ρ (w i) = r.val → Y (w i, w j) = S.rootChargeRow r (w j)) := by
      simp only [ae_all_iff]
      intro i j hij
      exact ae_of_ae_map ((measurable_pi_apply i).prodMk (measurable_pi_apply j)).aemeasurable
        ((hfresh i j hij).ae_le hrow)
    have hfactsProd := ae_of_ae_map PhysicalCliqueRepresentative.measurable_cons.aemeasurable hfacts
    have hnone : ∀ᵐ v ∂ρ, ∀ i, v i ∉ I :=
      ae_restrict_mem (measurableSet_no_root I hI)
    have hpositive : ∀ᵐ v ∂ρ, ∀ j : Fin n, 0 < S.rootChargeRow r (v j) := by
      have hstar := (P.ae_positive_private_stars hW hd hgap hpeak hhigh hprivate
        hA hell hmargin).1
      have hstarμ : ∀ᵐ x ∂μ, x ∈ Iᶜ → 0 < S.rootChargeRow r x :=
        (ae_restrict_iff' hI.compl).mp hstar
      have hvertices : ∀ᵐ v ∂P.laws n, ∀ j : Fin n,
          v j ∈ Iᶜ → 0 < S.rootChargeRow r (v j) := by
        simp only [ae_all_iff]
        intro j
        have hc := PhysicalPrimal.coordinate_marginal_absolutelyContinuous_of_balance
          P.laws _ P.feasible.1 P.feasible.2.1 P.feasible.2.2.2 n j
        have hd := (PhysicalPrimal.graphDemand_fst_le μ
          {z | PhysicalRepresentative.adjacency W m z.1 z.2 = true}).absolutelyContinuous
        exact ae_of_ae_map (measurable_pi_apply j).aemeasurable ((hc.trans hd).ae_le hstarμ)
      filter_upwards [hρ.ae_le hvertices, hnone] with v hv hn j
      exact hv j (hn j)
    have hfalse : ∀ᵐ p ∂ν.prod ρ, False := by
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae hνI,
        Measure.quasiMeasurePreserving_snd.ae hnone,
        Measure.quasiMeasurePreserving_snd.ae hpositive,
        Measure.quasiMeasurePreserving_snd.ae (hρ.ae_le (P.feasible.2.2.1 n)),
        Measure.quasiMeasurePreserving_snd.ae (hρ.ae_le (P.tight_physical n)),
        hlicenseProd, hfactsProd] with p hp hnoro hpstar hc ht hlic hfact
      have hnew (i : Fin n) : G (p.1, p.2 i) = true := by
        have h := hfact 0 i.succ (Fin.succ_ne_zero i).symm
        change (S.ρ p.1 = r.val → (G (p.1, p.2 i) = true ↔ p.2 i ∉ I)) ∧ _ at h
        exact (h.1 hp).mpr (hnoro i)
      have hnewstar (i : Fin n) : 0 < Y (p.1, p.2 i) := by
        have h := hfact 0 i.succ (Fin.succ_ne_zero i).symm
        change _ ∧ (S.ρ p.1 = r.val → Y (p.1, p.2 i) = S.rootChargeRow r (p.2 i)) at h
        rw [h.2 hp]
        exact hpstar i
      have hcl : PhysicalCliqueRepresentative.Clique G (Fin.cons p.1 p.2) := by
        intro i j hij
        cases i using Fin.cases with
        | zero =>
          cases j using Fin.cases with
          | zero => exact (hij rfl).elim
          | succ j => exact hnew j
        | succ i =>
          cases j using Fin.cases with
          | zero =>
            change PhysicalRepresentative.adjacency W m (p.2 i) p.1 = true
            rw [PhysicalRepresentative.adjacency_symm W m (p.2 i) p.1]
            exact hnew i
          | succ j => exact hc i j (fun h => hij (congrArg Fin.succ h))
      have hsum : 0 < ∑ i : Fin n, Y (p.1, p.2 i) := by
        let i : Fin n := ⟨0, by omega⟩
        exact (hnewstar i).trans_le (Finset.single_le_sum
          (fun j _ => (hnewstar j).le) (Finset.mem_univ i))
      have hcap := hlic hcl
      have he := PhysicalTriangleExposure.charge_cons Y
        (PhysicalRepresentative.charge_symm W m) p.2 p.1
      have hgt : 1 < PhysicalPrimal.charge Y (Fin.cons p.1 p.2) := by
        rw [he, ht]
        linarith
      exact (not_lt_of_ge hcap) hgt
    have hz : (ν.prod ρ) univ = 0 := by simpa only [ae_iff, not_false_eq_true, ofPred_true] using hfalse
    have hmass : (ν.prod ρ) univ = ρ univ := by
      rw [← univ_prod_univ, Measure.prod_prod, measure_univ, one_mul]
    have hρzero : ρ = 0 := Measure.measure_univ_eq_zero.mp (hmass.symm.trans hz)
    exact hρzero
  · have hn' : n ≤ 1 := by omega
    interval_cases n <;> simp [P.feasible.1, P.feasible.2.1, PhysicalRootReplacement.noRootLaw]

/-- Every positive-order private parent has a root in one of the two original fibers. -/
theorem ae_has_combined_root (P : S.PrivatePhysicalPrimal r p c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpeak : S.IsCommonForwardPeak d c r)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.H)
    (hprivate : ∀ᵐ q ∂μ.prod μ, S.ρ q.1 = r.val →
      adjacencyKernel W q.1 q.2 =
        if S.ρ q.2 = r.val ∨ S.ρ q.2 = p.val then 0 else 1)
    (hA : 1 / 3 < μ.real {x | S.ρ x = r.val})
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * (1 + m) * μ.real {x | S.ρ x = r.val} <
      3 * (2 * (c - m * d) + m))
    (n : ℕ) : ∀ᵐ v ∂P.laws n, ∃ j,
      S.ρ (v j) = r.val ∨ S.ρ (v j) = p.val := by
  have hz := congrArg (fun ν : Measure (Fin n → Ω) => ν univ)
    (P.noRootLaw_eq_zero hW hd hgap hpeak hhigh hprivate hA hell hmargin n)
  simp only [PhysicalRootReplacement.noRootLaw, Measure.restrict_apply_univ,
    Measure.coe_zero, Pi.zero_apply] at hz
  have hn := measure_eq_zero_iff_ae_notMem.mp hz
  filter_upwards [hn] with v hv
  simpa only [Set.mem_union, Set.mem_ofPred_eq, not_forall, not_not] using hv

/-- Root existence and strict two-vertex slack remove the order-two private law. -/
theorem law_two_eq_zero (P : S.PrivatePhysicalPrimal r p c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpeak : S.IsCommonForwardPeak d c r)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.H)
    (hprivate : ∀ᵐ q ∂μ.prod μ, S.ρ q.1 = r.val →
      adjacencyKernel W q.1 q.2 =
        if S.ρ q.2 = r.val ∨ S.ρ q.2 = p.val then 0 else 1)
    (hA : 1 / 3 < μ.real {x | S.ρ x = r.val})
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * (1 + m) * μ.real {x | S.ρ x = r.val} <
      3 * (2 * (c - m * d) + m))
    (hunsat : ∀ u : S.I, p ≠ u → ¬S.IsSaturatedAtomPair p u) :
    P.laws 2 = 0 := by
  let I := {x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val}
  have hI : MeasurableSet I :=
    (S.hfibers r.val r.property).1.union (S.hfibers p.val p.property).1
  have hle := PhysicalPrimal.mass_le_orderFirstOccupation_of_has_root 2 (P.laws 2) I
    hI (P.ae_has_combined_root hW hd hgap hpeak hhigh hprivate hA hell hmargin 2)
  have hfirst := P.orderRootLeaves_two_first_eq_zero hW hd hgap hell.2 hhigh
  have hsecond := P.orderRootLeaves_two_second_eq_zero hW hd hgap hell.2 hunsat
  have hsum := PhysicalPrimal.orderRootLeaves_union 2 (P.laws 2)
    {x | S.ρ x = r.val} {x | S.ρ x = p.val}
    (S.hfibers p.val p.property).1
    (by
      apply Set.disjoint_left.mpr
      intro x hx hy
      have hr : S.ρ x = r.val := hx
      have hp : S.ρ x = p.val := hy
      exact P.distinct_roots (Subtype.ext (hr.symm.trans hp)))
  have hz : PhysicalPrimal.orderRootLeaves 2 (P.laws 2) I = 0 := by
    rw [hsum, hfirst, hsecond, add_zero]
  have hz' := congrArg (fun η : Measure Ω => η univ) hz
  rw [PhysicalPrimal.orderRootLeaves_mass 2 (P.laws 2) I hI] at hz'
  norm_num only [Nat.reduceSub, Nat.cast_one, one_mul] at hz'
  rw [hz'] at hle
  exact Measure.measure_univ_eq_zero.mp (le_antisymm hle zero_le)

/-- The two exact original root quotas pay twice the private primal cost. -/
theorem objective_le_half_private_quota (P : S.PrivatePhysicalPrimal r p c)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpeak : S.IsCommonForwardPeak d c r)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.H)
    (hprivate : ∀ᵐ q ∂μ.prod μ, S.ρ q.1 = r.val →
      adjacencyKernel W q.1 q.2 =
        if S.ρ q.2 = r.val ∨ S.ρ q.2 = p.val then 0 else 1)
    (hA : 1 / 3 < μ.real {x | S.ρ x = r.val})
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * (1 + m) * μ.real {x | S.ρ x = r.val} <
      3 * (2 * (c - m * d) + m))
    (hunsat : ∀ u : S.I, p ≠ u → ¬S.IsSaturatedAtomPair p u) :
    2 * c ≤
      (μ.real {x | S.ρ x = r.val} + μ.real {x | S.ρ x = p.val}) *
        (1 - μ.real {x | S.ρ x = r.val} - μ.real {x | S.ρ x = p.val}) -
        μ.real {x | S.ρ x = p.val} *
          μ.real (({x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val})ᶜ \
            S.rootNeighborhood p) := by
  let Ir := {x | S.ρ x = r.val}
  let Ip := {x | S.ρ x = p.val}
  let I := Ir ∪ Ip
  have hr : MeasurableSet Ir := (S.hfibers r.val r.property).1
  have hp : MeasurableSet Ip := (S.hfibers p.val p.property).1
  have hI : MeasurableSet I := hr.union hp
  have hdis : Disjoint Ir Ip := Set.disjoint_left.mpr (by
    intro x hx hy
    exact P.distinct_roots (Subtype.ext (hx.symm.trans hy)))
  have hleaves : PhysicalPrimal.rootLeaves P.laws I =
      PhysicalPrimal.rootLeaves P.laws Ir + PhysicalPrimal.rootLeaves P.laws Ip := by
    unfold PhysicalPrimal.rootLeaves
    calc
      Measure.sum (fun n => PhysicalPrimal.orderRootLeaves n (P.laws n) I) =
          Measure.sum (fun n => PhysicalPrimal.orderRootLeaves n (P.laws n) Ir +
            PhysicalPrimal.orderRootLeaves n (P.laws n) Ip) := by
              congr 1
              funext n
              exact PhysicalPrimal.orderRootLeaves_union n (P.laws n) Ir Ip hp hdis
      _ = _ := (Measure.sum_add_sum _ _).symm
  have hquota : PhysicalPrimal.rootLeaves P.laws I =
      μ Ir • μ.restrict Iᶜ + μ Ip • μ.restrict (S.rootNeighborhood p) := by
    rw [hleaves, P.leaves_first, P.leaves_second]
  have : ∀ n, IsFiniteMeasure (P.laws n) := P.finite
  have hfirstfinite : IsFiniteMeasure (μ Ir • μ.restrict Iᶜ) := by
    constructor
    rw [Measure.smul_apply, Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.mpr
      (ENNReal.mul_ne_top (measure_ne_top μ Ir) (measure_ne_top μ Iᶜ))
  have hsecondfinite : IsFiniteMeasure
      (μ Ip • μ.restrict (S.rootNeighborhood p)) := by
    constructor
    rw [Measure.smul_apply, Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.mpr
      (ENNReal.mul_ne_top (measure_ne_top μ Ip)
        (measure_ne_top μ (S.rootNeighborhood p)))
  have : IsFiniteMeasure (PhysicalPrimal.rootLeaves P.laws I) := by
    constructor
    rw [hquota, Measure.add_apply]
    exact ENNReal.add_lt_top.mpr ⟨hfirstfinite.1, hsecondfinite.1⟩
  have hsmall : ∀ n, n < 3 → P.laws n = 0 := by
    intro n hn
    interval_cases n
    · exact P.feasible.1
    · exact P.feasible.2.1
    · exact P.law_two_eq_zero hW hd hgap hpeak hhigh hprivate hA hell hmargin hunsat
  have hroot (n : ℕ) : ∀ᵐ v ∂P.laws n, ∃ j : Fin n, v j ∈ I := by
    simpa only [Ir, Ip, I, Set.mem_union, Set.mem_ofPred_eq] using
      P.ae_has_combined_root hW hd hgap hpeak hhigh hprivate hA hell hmargin n
  have hcost := PhysicalPrimal.cost_le_half_rootLeaves_mass P.laws I hI hsmall hroot
  rw [P.cost] at hcost
  have hN := private_neighbor_mass S r p P.distinct_roots hW hd hgap hprivate
  have hquotaReal : (PhysicalPrimal.rootLeaves P.laws I).real univ =
      μ.real Ir * μ.real Iᶜ + μ.real Ip * μ.real (S.rootNeighborhood p) := by
    rw [hquota, measureReal_add_apply hfirstfinite.1.ne hsecondfinite.1.ne]
    simp only [measureReal_def, Measure.smul_apply, Measure.restrict_apply_univ,
      smul_eq_mul, ENNReal.toReal_mul]
  rw [hquotaReal] at hcost
  have hV : μ.real Iᶜ = 1 - μ.real Ir - μ.real Ip := by
    rw [measureReal_compl hI, probReal_univ, measureReal_union hdis hp]
    ring
  change μ.real (S.rootNeighborhood p) =
    1 - μ.real Ir - μ.real Ip - μ.real (Iᶜ \ S.rootNeighborhood p) at hN
  change 2 * c ≤ (μ.real Ir + μ.real Ip) *
    (1 - μ.real Ir - μ.real Ip) - μ.real Ip * μ.real (Iᶜ \ S.rootNeighborhood p)
  rw [hV, hN] at hcost
  linarith only [hcost]


end PrivatePhysicalPrimal

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- The actual selected private model constructs the primal used in the
unsaturated two-root cost bound. -/
theorem unsaturated_private_objective_le_half_quota
    (S : SelectedHighLowStructure W m) (r p : S.I) (hrp : r ≠ p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpeak : S.IsCommonForwardPeak d c r)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.H)
    (hprivate : ∀ᵐ q ∂μ.prod μ, S.ρ q.1 = r.val →
      adjacencyKernel W q.1 q.2 =
        if S.ρ q.2 = r.val ∨ S.ρ q.2 = p.val then 0 else 1)
    (hA : 1 / 3 < μ.real {x | S.ρ x = r.val})
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * (1 + m) * μ.real {x | S.ρ x = r.val} <
      3 * (2 * (c - m * d) + m))
    (hunsat : ∀ u : S.I, p ≠ u → ¬S.IsSaturatedAtomPair p u) :
    2 * c ≤
      (μ.real {x | S.ρ x = r.val} + μ.real {x | S.ρ x = p.val}) *
        (1 - μ.real {x | S.ρ x = r.val} - μ.real {x | S.ρ x = p.val}) -
        μ.real {x | S.ρ x = p.val} *
          μ.real (({x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val})ᶜ \
            S.rootNeighborhood p) := by
  obtain ⟨P⟩ := S.exists_private_physical_primal r p hrp hW hd hgap hprivate
  exact P.objective_le_half_private_quota hW hd hgap hpeak hhigh hprivate
    hA hell hmargin hunsat

end Erdos1017.CappedModel.SelectedHighLowStructure
