module

public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalPositiveStars
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalSATGeometry
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-!
# Triangle stock of the universal-root primal

A root triangle whose leaf event forces the third vertex into `P` uses at most
that triangle law's exact `P`-to-leaf pair stock, the universal-root primal
retains the exact pair demand of every other whole atom, and off-head triangles
dominate `(3A-1)` times each exterior event
(`off_partner_triangle_mass_lower_bound`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators ENNReal Classical

namespace Erdos1017.PhysicalPrimal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A root triangle whose leaf event forces the third vertex into P
uses at most that same triangle law's exact P-to-leaf pair stock. -/
theorem orderRootLeaves_three_le_partner_of_contains
    (ρ : Measure (Fin 3 → Ω)) (I P B : Set Ω) (hB : MeasurableSet B)
    (hstock : ∀ᵐ v ∂ρ, ∀ i j : Fin 3, i ≠ j → v i ∈ I → v j ∈ B →
      ∃ k : Fin 3, k ≠ i ∧ k ≠ j ∧ v k ∈ P) :
    orderRootLeaves 3 ρ I B ≤ orderRootLeaves 3 ρ P B := by
  let t : Fin 3 → Fin 3 → Fin 3 := fun i j =>
    if i = 0 then if j = 1 then 2 else 1
    else if i = 1 then if j = 0 then 2 else 0
    else if j = 0 then 1 else 0
  have ht : ∀ i j : Fin 3, i ≠ j → t i j ≠ j ∧ t (t i j) j = i ∧
      ∀ k : Fin 3, k ≠ i → k ≠ j → k = t i j := by decide
  let f : PairIndex 3 → PairIndex 3 := fun ij =>
    ⟨(t ij.val.1 ij.val.2, ij.val.2), (ht _ _ ij.property).1⟩
  have hf : ∀ ij, f (f ij) = ij := by
    intro ij
    apply Subtype.ext
    exact Prod.ext (ht _ _ ij.property).2.1 rfl
  let e : PairIndex 3 ≃ PairIndex 3 := ⟨f, f, hf, hf⟩
  have hterm (ij : PairIndex 3) :
      ((ρ.restrict {v | v ij.val.1 ∈ I}).map (fun v => v ij.val.2)) B ≤
        ((ρ.restrict {v | v (f ij).val.1 ∈ P}).map (fun v => v (f ij).val.2)) B := by
    rw [Measure.map_apply (measurable_pi_apply _) hB,
      Measure.restrict_apply (hB.preimage (measurable_pi_apply _)),
      Measure.map_apply (measurable_pi_apply _) hB,
      Measure.restrict_apply (hB.preimage (measurable_pi_apply _))]
    apply measure_mono_ae
    filter_upwards [hstock] with v hv hm
    obtain ⟨k, hki, hkj, hkp⟩ := hv ij.val.1 ij.val.2 ij.property hm.2 hm.1
    have hk := (ht _ _ ij.property).2.2 k hki hkj
    refine ⟨hm.1, ?_⟩
    change v (t ij.val.1 ij.val.2) ∈ P
    rw [← hk]
    exact hkp
  rw [orderRootLeaves, Measure.finsetSum_apply, orderRootLeaves, Measure.finsetSum_apply]
  calc
    (∑ ij : PairIndex 3,
        ((ρ.restrict {v | v ij.val.1 ∈ I}).map (fun v => v ij.val.2)) B) ≤
        ∑ ij : PairIndex 3,
          ((ρ.restrict {v | v (f ij).val.1 ∈ P}).map (fun v => v (f ij).val.2)) B :=
      Finset.sum_le_sum (fun ij _ => hterm ij)
    _ = ∑ ij : PairIndex 3,
        ((ρ.restrict {v | v ij.val.1 ∈ P}).map (fun v => v ij.val.2)) B :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)

/-- With no order-two incidence on the supplied event, the only excess
of three universal-root leaves over degree is its actual triangle stock. -/
theorem three_rootLeaves_le_degree_add_triangle
    (η : Laws Ω) (I : Set Ω) (hI : MeasurableSet I)
    (hunique : ∀ n, ∀ᵐ v ∂η n, ∀ i j, v i ∈ I → v j ∈ I → i = j)
    (B : Set Ω) (hI2 : orderRootLeaves 2 (η 2) I B = 0) :
    3 * rootLeaves η I B ≤
      (occupation η).fst B + orderRootLeaves 3 (η 3) I B := by
  have hord (n : ℕ) :
      3 * orderRootLeaves n (η n) I B ≤
        (orderOccupation n (η n)).fst B +
          if n = 3 then orderRootLeaves n (η n) I B else 0 := by
    have hroot := orderRootLeaves_le_orderFirstOccupation n (η n) I hI (hunique n) B
    by_cases hn : 4 ≤ n
    · have hnum : (3 : ℝ≥0∞) ≤ (n - 1 : ℕ) := by
        exact_mod_cast (show 3 ≤ n - 1 by omega)
      rw [fst_orderOccupation, Measure.smul_apply, nsmul_eq_mul]
      simp only [show n ≠ 3 by omega, ↓reduceIte, add_zero]
      exact (mul_le_mul_of_nonneg_left hroot (by norm_num : (0 : ℝ≥0∞) ≤ 3)).trans
        (mul_le_mul_of_nonneg_right hnum
          (show 0 ≤ orderFirstOccupation n (η n) B from zero_le))
    · interval_cases n
      · simp [orderRootLeaves, orderOccupation]
      · have he : (Finset.univ : Finset (PairIndex 1)) = ∅ := by
          ext ij
          exact False.elim (ij.property (Subsingleton.elim _ _))
        simp [orderRootLeaves, orderOccupation, he]
      · rw [hI2, mul_zero]
        exact zero_le
      · rw [fst_orderOccupation, Measure.smul_apply, nsmul_eq_mul]
        simp only [↓reduceIte]
        calc
          3 * orderRootLeaves 3 (η 3) I B =
              2 * orderRootLeaves 3 (η 3) I B + orderRootLeaves 3 (η 3) I B := by ring
          _ ≤ 2 * orderFirstOccupation 3 (η 3) B + orderRootLeaves 3 (η 3) I B :=
            by
              simpa only [add_comm] using add_le_add_right (mul_le_mul_right hroot 2)
                (orderRootLeaves 3 (η 3) I B)
  rw [rootLeaves, Measure.sum_apply_of_countable, ← ENNReal.tsum_mul_left,
    occupation, Measure.fst_sum, Measure.sum_apply_of_countable]
  calc
    (∑' n, 3 * orderRootLeaves n (η n) I B) ≤
        ∑' n, ((orderOccupation n (η n)).fst B +
          if n = 3 then orderRootLeaves n (η n) I B else 0) :=
      ENNReal.tsum_le_tsum hord
    _ = (∑' n, (orderOccupation n (η n)).fst B) +
        orderRootLeaves 3 (η 3) I B := by
      rw [ENNReal.tsum_add]
      simp

end Erdos1017.PhysicalPrimal

namespace Erdos1017.CappedModel.SelectedHighLowStructure.UniversalPhysicalPrimal

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m} {r : S.I} {c : ℝ}

/-- The same universal-root primal retains the exact original pair demand
of every other whole atom. No independently chosen second primal is used. -/
theorem partner_rootLeaves (P : S.UniversalPhysicalPrimal r c) (p : S.I)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    PhysicalPrimal.rootLeaves P.laws {x | S.ρ x = p.val} =
      μ {x | S.ρ x = p.val} • μ.restrict (S.rootNeighborhood p) := by
  have hE : MeasurableSet {z : Ω × Ω |
      PhysicalRepresentative.adjacency W m z.1 z.2 = true} :=
    (PhysicalRepresentative.measurable_adjacency W m) (measurableSet_singleton true)
  have hrow : ∀ᵐ z ∂(μ.restrict {x | S.ρ x = p.val}).prod μ,
      PhysicalRepresentative.adjacency W m z.1 z.2 = true ↔
        z.2 ∈ S.rootNeighborhood p := by
    filter_upwards [ae_mono (Measure.prod_mono Measure.restrict_le_self le_rfl)
      (S.ae_root_adjacency p hW hd hgap),
      Measure.quasiMeasurePreserving_fst.ae
        (ae_restrict_mem (S.hfibers p.val p.property).1)] with z hz hx
    exact hz hx
  exact PhysicalPrimal.rootLeaves_graphDemand_homogeneous P.laws μ _ hE P.feasible.2.2.2
    {x | S.ρ x = p.val} (S.rootNeighborhood p) (S.hfibers p.val p.property).1 hrow

/-- Original whole-fiber independence gives at most one partner coordinate
in each parent of that same physical law, including singular parents. -/
theorem partner_unique_root (P : S.UniversalPhysicalPrimal r c) (p : S.I)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (n : ℕ) :
    ∀ᵐ v ∂P.laws n, ∀ i j, S.ρ (v i) = p.val → S.ρ (v j) = p.val → i = j := by
  have hind : (μ.prod μ) ({z : Ω × Ω |
      PhysicalRepresentative.adjacency W m z.1 z.2 = true} ∩
        ({x | S.ρ x = p.val} ×ˢ {x | S.ρ x = p.val})) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [S.ae_root_fiber_physical_independent p hW hd hgap] with z hz hm
    have hfalse := hz hm.2.1 hm.2.2
    have htrue : PhysicalRepresentative.adjacency W m z.1 z.2 = true := hm.1
    rw [hfalse] at htrue
    exact Bool.false_ne_true htrue
  exact PhysicalPrimal.ae_at_most_one_root_graphDemand P.laws μ _ P.feasible.2.2.2
    {x | S.ρ x = p.val} (S.hfibers p.val p.property).1 hind n

end Erdos1017.CappedModel.SelectedHighLowStructure.UniversalPhysicalPrimal

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- Uniqueness of the saturated pair gives strict root-charge slack on the entire original
exterior of both heads, including the common neighborhood. -/
theorem ae_rootChargeRow_lt_one_off_universalPartner
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1) :
    ∀ᵐ x ∂μ.restrict (({x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val})ᶜ),
      S.rootChargeRow r x < 1 := by
  let : Countable S.I := S.hI.to_subtype
  let Ir := {x | S.ρ x = r.val}
  have hIr := S.hfibers r.val r.property
  have hnot (u : S.I) (hru : r ≠ u) (hpu : p ≠ u) :
      ¬S.IsSaturatedAtomPair r u := by
    intro hru'
    rcases hpair.unique hru' hW hd hgap hell with ⟨_, h⟩ | ⟨h, _⟩
    · exact hpu h
    · exact hru h
  have hatom : ∀ᵐ x ∂μ, ∀ u : S.I,
      S.ρ x = u.val →
        x ∈ ({x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val})ᶜ → S.rootChargeRow r x < 1 := by
    apply ae_all_iff.mpr
    intro u
    by_cases hru : r = u
    · subst u
      filter_upwards [S.rootChargeRow_zero_off_neighborhood r hW hd hgap] with x hx hxr hh
      exact False.elim (hh (Or.inl hxr))
    · by_cases hpu : p = u
      · subst u
        filter_upwards [S.rootChargeRow_zero_off_neighborhood r hW hd hgap] with x hx hxp hh
        exact False.elim (hh (Or.inr hxp))
      · exact (ae_restrict_iff' (S.hfibers u.val u.property).1).mp
          (S.ae_rootChargeRow_lt_one_of_not_saturated r u hru hW hd hgap
            (hnot u hru hpu)) |>.mono (fun _ hx hu hh => hx hu)
  have hdiff : ∀ᵐ x ∂μ, x ∈ S.D → S.rootChargeRow r x < 1 := by
    have hp : ∀ᵐ q ∂μ.prod μ, q.1 ∈ Ir → q.2 ∈ S.D →
        S.rootChargeRow r q.2 < 1 := by
      filter_upwards [S.ae_root_charge r hW hd hgap,
        PhysicalRepresentative.charge_ae_eq W m
          (hW.strict_gap_structure hd hgap).strict_support,
        S.charge_lt_one_on_atom_diffuse hW hd hgap hell r] with q hr he hc hx hy
      rw [← hr hx, he]
      exact hc hx hy
    obtain ⟨x, hx, hrow⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      hIr.2.1.ne' ((ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hp)).and
        (ae_restrict_mem hIr.1))
    exact hrow.1.mono (fun _ hy hD => hy hrow.2 hD)
  apply (ae_restrict_iff'
    (((S.hfibers r.val r.property).1.union (S.hfibers p.val p.property).1).compl)).mpr
  filter_upwards [hatom, hdiff] with x ha hD hx
  by_cases hxD : x ∈ S.D
  · exact hD hxD
  · have hu : x ∈ ⋃ u ∈ S.I, {y | S.ρ y = u} := by
      simpa only [S.hDeq, mem_compl_iff, not_not] using hxD
    obtain ⟨u, hxu⟩ := mem_iUnion.mp hu
    obtain ⟨huI, hxu⟩ := mem_iUnion.mp hxu
    exact ha ⟨u, huI⟩ hxu hx

/-- The licensed off-partner root repricer gives degree at least twice
the original universal mass on the entire two-head exterior. -/
theorem ae_universalPartner_exterior_degree_ge_twice_mass
    (S : SelectedHighLowStructure W m) (r p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N) :
    ∀ᵐ x ∂μ.restrict (({x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val})ᶜ),
      2 * μ.real {z | S.ρ z = r.val} ≤ ∫ z, adjacencyKernel W x z ∂μ := by
  let I := {x | S.ρ x = r.val}
  have hI : MeasurableSet I := (S.hfibers r.val r.property).1
  have hn := S.ae_universal_rootNeighborhood_iff r hW hd hgap hN
  have hsets : S.rootNeighborhood r =ᵐ[μ] Iᶜ := hn.mono (fun _ hx => propext hx)
  have hrow := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    (S.neutral_atom_adjacency r hW hd hgap hN)
  have hsym := adjacencyKernel_symm W
  apply (ae_restrict_iff'
    (((S.hfibers r.val r.property).1.union (S.hfibers p.val p.property).1).compl)).mpr
  filter_upwards [S.ae_original_root_degree_ge_mass r hW hd hgap, hn,
    (ae_restrict_iff'
      (((S.hfibers r.val r.property).1.union (S.hfibers p.val p.property).1).compl)).mp
      (S.ae_rootChargeRow_lt_one_off_universalPartner r p hpair hW hd hgap hell),
    Measure.ae_ae_of_ae_prod (hrow.and hsym)] with x hl hn hs hr hH
  have hxI : S.ρ x ≠ r.val := by
    intro he
    exact hH (Or.inl he)
  have hbound := hl (hn.mpr hxI) (hs hH)
  rw [Measure.restrict_congr_set hsets] at hbound
  have hroot : (∫ z in I, adjacencyKernel W x z ∂μ) = μ.real I := by
    have heq : ∀ᵐ z ∂μ.restrict I, adjacencyKernel W x z = 1 := by
      filter_upwards [ae_restrict_of_ae hr, ae_restrict_mem hI] with z hz hm
      have he := hz.1 hm
      change adjacencyKernel W z x = (if S.ρ x = r.val then 0 else 1) at he
      exact hz.2.trans (by simpa only [hxI, ite_false] using he)
    rw [integral_congr_ae heq, setIntegral_const, smul_eq_mul, mul_one]
  have hi : Integrable (adjacencyKernel W x) μ := Integrable.of_bound
    ((W.stronglyMeasurable_moment
      CappedColor.continuous_adjacency.measurable.stronglyMeasurable).comp_measurable
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
    (Eventually.of_forall (fun z => by
      change ‖W.moment CappedColor.adjacency (x, z)‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (adjacency_moment_mem W (x, z)).1]
      exact (adjacency_moment_mem W (x, z)).2))
  have he := integral_add_compl hI hi
  rw [hroot] at he
  change μ.real I ≤ ∫ z in Iᶜ, adjacencyKernel W x z ∂μ at hbound
  linarith

namespace UniversalPhysicalPrimal

variable {S : SelectedHighLowStructure W m} {r : S.I} {c : ℝ}

/-- The saturated I–P pair remains available at order two; only leaves
outside both heads vanish, using the licensed original charge slack. -/
theorem orderRootLeaves_two_off_partner_eq_zero
    (P : S.UniversalPhysicalPrimal r c) (p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1) (B : Set Ω) (hB : MeasurableSet B)
    (hBV : B ⊆ ({x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val})ᶜ) :
    PhysicalPrimal.orderRootLeaves 2 (P.laws 2) {x | S.ρ x = r.val} B = 0 := by
  have hV : MeasurableSet ({x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val})ᶜ :=
    ((S.hfibers r.val r.property).1.union (S.hfibers p.val p.property).1).compl
  have hslack := P.ae_original_vertices _ ((ae_restrict_iff' hV).mp
    (S.ae_rootChargeRow_lt_one_off_universalPartner r p hpair hW hd hgap hell)) 2
  have hrow := P.ae_original_pairs _ (S.ae_root_charge r hW hd hgap) 2
  have hno : ∀ᵐ v ∂P.laws 2, ∀ i j, i ≠ j → S.ρ (v i) = r.val → v j ∈ B → False := by
    filter_upwards [hslack, hrow, P.tight_physical 2] with v hs hr ht i j hij hi hj
    have hcharge : PhysicalPrimal.charge
        (Function.uncurry (PhysicalRepresentative.charge W m)) v =
        PhysicalRepresentative.charge W m (v 0) (v 1) := by
      rw [MultipartiteHeadPrice.physicalCharge_eq_tupleCharge]
      simp [FiniteArity.tupleCharge, FiniteArity.pairCharge, FiniteArity.crossSum,
        Fin.sum_univ_succ, PhysicalRepresentative.charge_symm W m (v 1) (v 0)]
    have hfull : ∀ i j : Fin 2, i ≠ j → PhysicalRepresentative.charge W m (v i) (v j) = 1 := by
      intro i j hij
      fin_cases i <;> fin_cases j
      · exact False.elim (hij rfl)
      · exact hcharge.symm.trans ht
      · exact (PhysicalRepresentative.charge_symm W m (v 1) (v 0)).trans (hcharge.symm.trans ht)
      · exact False.elim (hij rfl)
    have hlt := hs j (hBV hj)
    have he := hr i j hij hi
    linarith [hfull i j hij]
  rw [PhysicalPrimal.orderRootLeaves, Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro ij _
  rw [Measure.map_apply (measurable_pi_apply _) hB,
    Measure.restrict_apply (hB.preimage (measurable_pi_apply _))]
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [hno] with v hv hm
  exact hv ij.val.1 ij.val.2 ij.property hm.2 hm.1

/-- Actual original off-head triangles dominate (3A−1) times each
exterior event. The partner pair stock is kept in the same law. -/
theorem off_partner_triangle_mass_lower_bound
    (P : S.UniversalPhysicalPrimal r c) (p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1) (B : Set Ω) (hB : MeasurableSet B)
    (hBV : B ⊆ ({x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val})ᶜ) :
    (3 * S.originalAtomMass r - 1) * μ.real B ≤
      (PhysicalPrimal.orderRootLeaves 3 (P.laws 3) {x | S.ρ x = r.val}).real B := by
  have hI : MeasurableSet {x | S.ρ x = r.val} := (S.hfibers r.val r.property).1
  have hBI : B ⊆ {x | S.ρ x = r.val}ᶜ := fun x hx hi => hBV hx (Or.inl hi)
  have hcount := PhysicalPrimal.three_rootLeaves_le_degree_add_triangle P.laws _ hI
    P.unique_root B (P.orderRootLeaves_two_off_partner_eq_zero p hpair hW hd hgap hell B hB hBV)
  rw [P.leaves, Measure.smul_apply, Measure.restrict_apply hB] at hcount
  have hBext : B ∩ {x | S.ρ x ≠ r.val} = B := Set.inter_eq_left.mpr hBI
  rw [hBext, smul_eq_mul, P.feasible.2.2.2] at hcount
  have hraw : 3 * (μ {x | S.ρ x = r.val} * μ B) ≤
      μ B + PhysicalPrimal.orderRootLeaves 3 (P.laws 3) {x | S.ρ x = r.val} B :=
    hcount.trans (add_le_add (PhysicalPrimal.graphDemand_fst_le μ _ B) le_rfl)
  have : IsFiniteMeasure (P.laws 3) := P.finite 3
  have hfinRoot : PhysicalPrimal.orderRootLeaves 3 (P.laws 3) {x | S.ρ x = r.val} B ≠ ∞ := by
    unfold PhysicalPrimal.orderRootLeaves
    exact measure_ne_top _ B
  have hreal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨measure_ne_top μ B, hfinRoot⟩) hraw
  rw [ENNReal.toReal_add (measure_ne_top μ B) hfinRoot] at hreal
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at hreal
  change 3 * (S.originalAtomMass r * μ.real B) ≤ μ.real B +
    (PhysicalPrimal.orderRootLeaves 3 (P.laws 3) {x | S.ρ x = r.val}).real B at hreal
  nlinarith

/-- On the same tight triangle law, an I–P saturated pair pays its whole
unit charge, leaving exactly zero total charge to the third vertex. -/
theorem ae_triangle_partner_score_zero
    (P : S.UniversalPhysicalPrimal r c) (p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ v ∂P.laws 3, ∀ e : Equiv.Perm (Fin 3),
      S.ρ (v (e 0)) = r.val → S.ρ (v (e 1)) = p.val →
        S.rootChargeRow r (v (e 2)) + S.rootChargeRow p (v (e 2)) = 0 := by
  have hsat : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = r.val → S.ρ z.2 = p.val →
      PhysicalRepresentative.charge W m z.1 z.2 = 1 := by
    filter_upwards [hpair.2, PhysicalRepresentative.charge_ae_eq W m
      (hW.strict_gap_structure hd hgap).strict_support] with z hz he hr hp
    exact he.trans (hz hr hp)
  filter_upwards [P.ae_original_pairs _ hsat 3,
    P.ae_original_pairs _ (S.ae_root_charge r hW hd hgap) 3,
    P.ae_original_pairs _ (S.ae_root_charge p hW hd hgap) 3,
    P.tight_physical 3] with v hs hr hp ht e hi hj
  have he01 : e 0 ≠ e 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (e.injective h)
  have he02 : e 0 ≠ e 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (e.injective h)
  have he12 : e 1 ≠ e 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (e.injective h)
  have hcharge := (PhysicalTriangleExposure.charge_comp_equiv
    (Function.uncurry (PhysicalRepresentative.charge W m)) v e).trans ht
  have hvec : (fun i => v (e i)) = ![v (e 0), v (e 1), v (e 2)] := by
    funext i
    fin_cases i <;> rfl
  rw [hvec, PhysicalTriangleExposure.charge_three _
    (PhysicalRepresentative.charge_symm W m)] at hcharge
  change PhysicalRepresentative.charge W m (v (e 0)) (v (e 1)) +
    PhysicalRepresentative.charge W m (v (e 0)) (v (e 2)) +
    PhysicalRepresentative.charge W m (v (e 1)) (v (e 2)) = 1 at hcharge
  rw [hs _ _ he01 hi hj, hr _ _ he02 hi, hp _ _ he12 hj] at hcharge
  linarith

/-- A measurable off-head property proved on every actual tight root
triangle holds on the original vertex law when the root mass exceeds 1/3.
The triangle stock supplies this license without joint absolute continuity. -/
theorem ae_off_partner_of_triangle
    (P : S.UniversalPhysicalPrimal r c) (p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1) (hA : 1 / 3 < S.originalAtomMass r)
    (F : Ω → Prop) (hF : MeasurableSet {x | F x})
    (htriangle : ∀ᵐ v ∂P.laws 3, ∀ i j : Fin 3, i ≠ j →
      S.ρ (v i) = r.val →
        v j ∈ ({x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val})ᶜ → F (v j)) :
    ∀ᵐ x ∂μ.restrict ({x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val})ᶜ, F x := by
  classical
  let V := ({x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val})ᶜ
  let B := V ∩ {x | ¬F x}
  have hV : MeasurableSet V :=
    ((S.hfibers r.val r.property).1.union (S.hfibers p.val p.property).1).compl
  have hB : MeasurableSet B := hV.inter hF.compl
  have hz : PhysicalPrimal.orderRootLeaves 3 (P.laws 3) {x | S.ρ x = r.val} B = 0 := by
    rw [PhysicalPrimal.orderRootLeaves, Measure.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro ij _
    rw [Measure.map_apply (measurable_pi_apply _) hB,
      Measure.restrict_apply (hB.preimage (measurable_pi_apply _))]
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [htriangle] with v hv hm
    exact hm.1.2 (hv ij.val.1 ij.val.2 ij.property hm.2 hm.1.1)
  have hbound := P.off_partner_triangle_mass_lower_bound p hpair hW hd hgap hell B hB
    inter_subset_left
  have hzeroReal :
      (PhysicalPrimal.orderRootLeaves 3 (P.laws 3) {x | S.ρ x = r.val}).real B = 0 := by
    change (PhysicalPrimal.orderRootLeaves 3 (P.laws 3) {x | S.ρ x = r.val} B).toReal = 0
    rw [hz, ENNReal.toReal_zero]
  rw [hzeroReal] at hbound
  have hBzero : μ B = 0 := by
    by_contra hn
    have hpos : 0 < μ.real B := ENNReal.toReal_pos hn (measure_ne_top μ B)
    nlinarith
  apply (ae_restrict_iff' hV).mpr
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hBzero] with x hx hv
  by_contra hn
  exact hx ⟨hv, hn⟩

/-- If every offending root triangle uses P, the same original pair stock
forces degree at least 3A−b almost everywhere on that original event. -/
theorem ae_degree_lower_of_triangle_partner
    (P : S.UniversalPhysicalPrimal r c) (p : S.I)
    (hpair : S.IsSaturatedAtomPair r p)
    {d : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : -m < 1) (B : Set Ω) (hB : MeasurableSet B)
    (hBV : B ⊆ ({x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val})ᶜ)
    (hstock : ∀ᵐ v ∂P.laws 3, ∀ i j : Fin 3, i ≠ j →
      S.ρ (v i) = r.val → v j ∈ B →
        ∃ k : Fin 3, k ≠ i ∧ k ≠ j ∧ S.ρ (v k) = p.val) :
    ∀ᵐ x ∂μ.restrict B, 3 * S.originalAtomMass r - S.originalAtomMass p ≤
      (PhysicalPrimal.graphDegree μ
        {z | PhysicalRepresentative.adjacency W m z.1 z.2 = true} x).toReal := by
  let E := {z : Ω × Ω | PhysicalRepresentative.adjacency W m z.1 z.2 = true}
  have hE : MeasurableSet E :=
    (PhysicalRepresentative.measurable_adjacency W m) (measurableSet_singleton true)
  have hI : MeasurableSet {x | S.ρ x = r.val} := (S.hfibers r.val r.property).1
  have hquota (C : Set Ω) (hC : MeasurableSet C) :
      3 * μ {x | S.ρ x = r.val} * μ (C ∩ B) ≤
        (PhysicalPrimal.graphDemand μ E).fst (C ∩ B) +
          μ {x | S.ρ x = p.val} * μ (C ∩ B) := by
    have hCB := hC.inter hB
    have hCBV : C ∩ B ⊆ ({x | S.ρ x = r.val} ∪ {x | S.ρ x = p.val})ᶜ :=
      fun x hx => hBV hx.2
    have hcount := PhysicalPrimal.three_rootLeaves_le_degree_add_triangle P.laws _ hI
      P.unique_root (C ∩ B)
      (P.orderRootLeaves_two_off_partner_eq_zero p hpair hW hd hgap hell _ hCB hCBV)
    have hcharge := PhysicalPrimal.orderRootLeaves_three_le_partner_of_contains
      (P.laws 3) {x | S.ρ x = r.val} {x | S.ρ x = p.val} (C ∩ B) hCB
      (hstock.mono (fun _ hv i j hij hi hj => hv i j hij hi hj.2))
    have hstockAll : PhysicalPrimal.orderRootLeaves 3 (P.laws 3) {x | S.ρ x = p.val} ≤
        PhysicalPrimal.rootLeaves P.laws {x | S.ρ x = p.val} :=
      Measure.le_sum (fun n => PhysicalPrimal.orderRootLeaves n (P.laws n)
        {x | S.ρ x = p.val}) 3
    have hstockCap :
        PhysicalPrimal.orderRootLeaves 3 (P.laws 3) {x | S.ρ x = r.val} (C ∩ B) ≤
          μ {x | S.ρ x = p.val} * μ (C ∩ B) := by
      apply (hcharge.trans (hstockAll (C ∩ B))).trans
      rw [P.partner_rootLeaves p hW hd hgap, Measure.smul_apply, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (Measure.restrict_le_self (C ∩ B)) zero_le
    rw [P.leaves, Measure.smul_apply, Measure.restrict_apply hCB] at hcount
    have hCBext : (C ∩ B) ∩ {x | S.ρ x ≠ r.val} = C ∩ B :=
      inter_eq_left.mpr (fun x hx hi => hCBV hx (Or.inl hi))
    rw [hCBext, smul_eq_mul, P.feasible.2.2.2] at hcount
    simpa only [E, mul_assoc] using hcount.trans (add_le_add le_rfl hstockCap)
  have hdegree : ∀ᵐ x ∂μ.restrict B,
      3 * μ {x | S.ρ x = r.val} ≤
        PhysicalPrimal.graphDegree μ E x + μ {x | S.ρ x = p.val} := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite measurable_const
    intro C hC _
    rw [Measure.restrict_restrict hC,
      lintegral_add_left (PhysicalPrimal.measurable_graphDegree μ E hE)]
    simp only [lintegral_const, Measure.restrict_apply_univ]
    have hgraph : (PhysicalPrimal.graphDemand μ E).fst (C ∩ B) =
        ∫⁻ x in C ∩ B, PhysicalPrimal.graphDegree μ E x ∂μ := by
      rw [PhysicalPrimal.graphDemand_fst_eq_withDensity μ E hE,
        withDensity_apply _ (hC.inter hB)]
    simpa only [hgraph, mul_assoc] using hquota C hC
  filter_upwards [hdegree] with x hx
  have hfin : PhysicalPrimal.graphDegree μ E x ≠ ∞ := measure_ne_top μ _
  have hreal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hfin, measure_ne_top μ _⟩) hx
  rw [ENNReal.toReal_add hfin (measure_ne_top μ _)] at hreal
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at hreal
  change 3 * S.originalAtomMass r ≤
    (PhysicalPrimal.graphDegree μ E x).toReal + S.originalAtomMass p at hreal
  linarith

end UniversalPhysicalPrimal

end Erdos1017.CappedModel.SelectedHighLowStructure

namespace Erdos1017.CappedModel.PhysicalRepresentative

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] {W : Model Ω μ} {m : ℝ}

/-- The actual physical graph degree agrees with the original adjacency
integral on one original vertex event. No endpoint degree is substituted. -/
theorem ae_graphDegree_eq_original {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ x ∂μ, (PhysicalPrimal.graphDegree μ
      {z | adjacency W m z.1 z.2 = true} x).toReal =
        ∫ z, adjacencyKernel W x z ∂μ := by
  have hsections := Measure.ae_ae_of_ae_prod
    (adjacency_moment_ae_eq W m (hW.strict_gap_structure hd hgap).strict_support)
  filter_upwards [hsections] with x hx
  let N := {z | adjacency W m x z = true}
  have hN : MeasurableSet N := (measurable_adjacency W m).comp
    (measurable_const.prodMk measurable_id) (measurableSet_singleton true)
  have heq : (fun z => adjacencyKernel W x z) =ᵐ[μ] N.indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [hx] with z hz
    change W.moment CappedColor.adjacency (x, z) = _
    rw [hz]
    by_cases hA : adjacency W m x z = true <;> simp [N, hA]
  change μ.real N = _
  rw [integral_congr_ae heq, integral_indicator hN, setIntegral_const, smul_eq_mul, mul_one]

end Erdos1017.CappedModel.PhysicalRepresentative
