module

public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredPartition
public import Erdos1017.Exclusions.Common.CappedConditionalAveragingStationarity
public import Erdos1017.Exclusions.Common.StationaryMultiplierUniqueness

/-!
# Stationary average on a null-region boundary

This module defines the boundary label that keeps every atom and gives the whole
diffuse region one label, in the `E`-null mode or the `R`-null mode, and shows
that countable and deterministic charge averaging produce an own full stationary
model at the proved multiplier, whose boundary-label cliques pass the
conditional charge test.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ}

/-- Every original atom is retained; the entire original diffuse region
has one label. No finite-cardinality hypothesis is involved. -/
def coveredCountableBoundaryLabel (S : SelectedHighLowStructure W m) (x : Ω) : S.I ⊕ Unit :=
  if h : S.ρ x ∈ S.I then Sum.inl ⟨S.ρ x, h⟩ else Sum.inr ()

/-- True is the E-null boundary, where A sees D. False is the R-null
boundary, where A misses D. -/
def coveredBoundaryExpand (S : SelectedHighLowStructure W m) (mode : Bool) :
    S.I ⊕ Unit → S.I ⊕ Bool
  | Sum.inl u => Sum.inl u
  | Sum.inr _ => Sum.inr mode

def coveredCountableBoundaryGraph (S : SelectedHighLowStructure W m) (mode : Bool)
    (r a : S.I) (i j : S.I ⊕ Unit) : Bool :=
  S.coveredGraph r a (S.coveredBoundaryExpand mode i) (S.coveredBoundaryExpand mode j)

/-- Boundary coefficients are literal original conditional pair means. -/
def coveredCountableBoundaryCoefficient (S : SelectedHighLowStructure W m)
    (i j : S.I ⊕ Unit) : ℝ :=
  FiniteArity.regionPairCharge μ (chargeKernel W)
    (fun k => S.coveredCountableBoundaryLabel ⁻¹' {k}) i j

theorem coveredCountableBoundaryLabel_eq_inl_iff (S : SelectedHighLowStructure W m)
    (u : S.I) (x : Ω) :
    S.coveredCountableBoundaryLabel x = Sum.inl u ↔ S.ρ x = u.val := by
  by_cases hx : S.ρ x ∈ S.I
  · simp only [coveredCountableBoundaryLabel, hx, ↓reduceDIte, Sum.inl.injEq, Subtype.ext_iff]
  · simp only [coveredCountableBoundaryLabel, hx, ↓reduceDIte, reduceCtorEq, false_iff]
    exact fun he => hx (he.symm ▸ u.property)

theorem coveredCountableBoundaryLabel_eq_inr_iff (S : SelectedHighLowStructure W m)
    (x : Ω) : S.coveredCountableBoundaryLabel x = Sum.inr () ↔ x ∈ S.D := by
  have hD : x ∈ S.D ↔ S.ρ x ∉ S.I := by
    rw [S.hDeq]
    simp only [mem_compl_iff, mem_iUnion, mem_ofPred_eq]
    constructor
    · intro h hi; exact h ⟨S.ρ x, hi, rfl⟩
    · rintro h ⟨u, hu, he⟩; exact h (he ▸ hu)
  by_cases hx : S.ρ x ∈ S.I <;> simp [coveredCountableBoundaryLabel, hx, hD]

theorem measurable_coveredCountableBoundaryLabel (S : SelectedHighLowStructure W m) :
    @Measurable Ω (S.I ⊕ Unit) _ ⊤ S.coveredCountableBoundaryLabel := by
  let : MeasurableSpace (Lp ℝ 2 μ) := borel _
  let : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩
  let : MeasurableSpace (S.I ⊕ Unit) := ⊤
  let : Countable S.I := S.hI.to_subtype
  let s := {x | S.ρ x ∈ S.I}
  have hs : MeasurableSet s := S.hρ.measurable S.hI.measurableSet
  have hr : Measurable (fun x : s => (Sum.inl (⟨S.ρ x, x.property⟩ : S.I) : S.I ⊕ Unit)) :=
    (measurable_of_countable (Sum.inl : S.I → S.I ⊕ Unit)).comp
      ((S.hρ.measurable.comp measurable_subtype_coe).subtype_mk)
  have hd : Measurable (fun _ : (sᶜ : Set Ω) => (Sum.inr () : S.I ⊕ Unit)) := measurable_const
  convert hr.dite hd hs using 1
  funext x
  by_cases hx : S.ρ x ∈ S.I <;> simp [coveredCountableBoundaryLabel, s, hx]

theorem coveredCountableBoundaryLabel_fibers_positive (S : SelectedHighLowStructure W m)
    (hD : 0 < μ S.D) (i : S.I ⊕ Unit) :
    0 < μ (S.coveredCountableBoundaryLabel ⁻¹' {i}) := by
  cases i with
  | inl u =>
    have he : S.coveredCountableBoundaryLabel ⁻¹' {Sum.inl u} = {x | S.ρ x = u.val} := by
      ext x
      exact S.coveredCountableBoundaryLabel_eq_inl_iff u x
    rw [he]
    exact (S.hfibers u.val u.property).2.1
  | inr u =>
    cases u
    have he : S.coveredCountableBoundaryLabel ⁻¹' {Sum.inr ()} = S.D := by
      ext x
      exact S.coveredCountableBoundaryLabel_eq_inr_iff x
    rwa [he]

theorem coveredCountableBoundaryGraph_symm (S : SelectedHighLowStructure W m)
    (mode : Bool) (r a : S.I) (i j : S.I ⊕ Unit) :
    S.coveredCountableBoundaryGraph mode r a i j =
      S.coveredCountableBoundaryGraph mode r a j i := S.coveredGraph_symm r a _ _

/-- The original label agrees with the collapsed label off the single
mode-specific null region. This is only a pointwise implication. -/
theorem coveredBoundaryExpand_label (S : SelectedHighLowStructure W m) (a : S.I)
    (mode : Bool) (x : Ω) (hx : S.coveredLabel a x ≠ Sum.inr (!mode)) :
    S.coveredLabel a x = S.coveredBoundaryExpand mode (S.coveredCountableBoundaryLabel x) := by
  generalize hq : S.coveredLabel a x = i
  cases i with
  | inl u =>
    rw [(S.coveredCountableBoundaryLabel_eq_inl_iff u x).mpr
      ((S.coveredLabel_eq_inl_iff a u x).mp hq)]
    rfl
  | inr b =>
    rw [(S.coveredCountableBoundaryLabel_eq_inr_iff x).mpr
      ((S.coveredLabel_eq_inr_iff a x b).mp hq).1]
    have hb : b = mode := by cases b <;> cases mode <;> simp_all
    simp [coveredBoundaryExpand, hb]

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- Both boundary modes retain the actual countable original graph.
The common event removes only the explicitly null diffuse region. -/
theorem ae_covered_countable_boundary_graph (S : SelectedHighLowStructure W m)
    (mode : Bool) (r a : S.I) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hnull : μ (if mode = true then S.D \ S.rootNeighborhood a
      else S.D ∩ S.rootNeighborhood a) = 0) :
    ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if S.coveredCountableBoundaryGraph mode r a
        (S.coveredCountableBoundaryLabel p.1) (S.coveredCountableBoundaryLabel p.2) = true
      then 1 else 0 := by
  have hn : ∀ᵐ x ∂μ, S.coveredLabel a x ≠ Sum.inr (!mode) := by
    apply measure_eq_zero_iff_ae_notMem.mp
    change μ (S.coveredLabel a ⁻¹' {Sum.inr (!mode)}) = 0
    cases mode
    · simpa only [Bool.not_false, S.coveredLabel_fiber_true,
        Bool.false_eq_true, ite_false] using hnull
    · simpa only [Bool.not_true, S.coveredLabel_fiber_false, ite_true] using hnull
  filter_upwards [S.ae_covered_graph r a hW hd hgap hpair hzero,
    Measure.quasiMeasurePreserving_fst.ae hn,
    Measure.quasiMeasurePreserving_snd.ae hn] with p hp h1 h2
  rw [S.coveredBoundaryExpand_label a mode p.1 h1,
    S.coveredBoundaryExpand_label a mode p.2 h2] at hp
  exact hp

/-- True countable averaging and deterministic charge averaging produce
an own full stationary model at the proved original multiplier. Every
original label and all literal conditional moments remain on the same law. -/
theorem exists_covered_countable_boundary_stationary_average (S : SelectedHighLowStructure W m)
    (mode : Bool) (r a : S.I) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) (hD : 0 < μ S.D)
    (hnull : μ (if mode = true then S.D \ S.rootNeighborhood a
      else S.D ∩ S.rootNeighborhood a) = 0) :
    ∃ V : Model Ω μ, FullStationaryClass d c V m ∧
      (∀ p : Ω × Ω,
        V.moment CappedColor.adjacency p =
          (if S.coveredCountableBoundaryGraph mode r a
            (S.coveredCountableBoundaryLabel p.1) (S.coveredCountableBoundaryLabel p.2) = true
          then 1 else 0) ∧
        V.moment CappedColor.charge p = S.coveredCountableBoundaryCoefficient
          (S.coveredCountableBoundaryLabel p.1) (S.coveredCountableBoundaryLabel p.2)) ∧
      (∀ x, (∫ y, shiftedKernel V m x y ∂μ) = 2 * (c - m * d)) ∧
      ∀ p, ∀ᵐ z ∂V.kernel p,
        CappedColor.charge z = conditionalCharge V p * CappedColor.adjacency z := by
  let : MeasurableSpace (S.I ⊕ Unit) := ⊤
  let : Countable S.I := S.hI.to_subtype
  obtain ⟨U, hfull, hdU, hcU, hmom, hrow⟩ := exists_full_conditional_average_stationary
    W hW.full m (2 * (c - m * d)) hW.stationary S.coveredCountableBoundaryLabel
    S.measurable_coveredCountableBoundaryLabel (S.coveredCountableBoundaryLabel_fibers_positive hD)
    (S.coveredCountableBoundaryGraph mode r a) (S.coveredCountableBoundaryGraph_symm mode r a)
    (S.ae_covered_countable_boundary_graph mode r a hW hd hgap hpair hzero hnull)
  let V := averaged U
  have hVfull : FullFeasible V := fun n => feasible_averaged U (hfull n)
  have hdV : density V = d := (density_averaged U).trans (hdU.trans hW.density_eq)
  have hcV : objective V = c := (objective_averaged U).trans (hcU.trans hW.objective_eq)
  have hopt : objective V = FractionalGraph.densityLimit (density V) := by
    rw [hcV, hdV]
    exact hW.optimal
  have hVrow (x : Ω) : (∫ y, shiftedKernel V m x y ∂μ) = 2 * (c - m * d) := by
    convert hrow x using 1
    apply integral_congr_ae
    filter_upwards with y
    simp only [V, shiftedKernel, shiftedMoment_eq, charge_moment_averaged,
      adjacency_moment_averaged]
  have hphysical (p : Ω × Ω) : ∀ᵐ z ∂V.kernel p,
      CappedColor.charge z = conditionalCharge V p * CappedColor.adjacency z := by
    change ∀ᵐ z ∂(averaged U).kernel p,
      CappedColor.charge z = conditionalCharge (averaged U) p * CappedColor.adjacency z
    rw [conditionalCharge_averaged]
    exact averaged_deterministic U p
  have hdV' : density V ∈ Ioo (1 / 4 : ℝ) (1 / 2) := hdV ▸ hd
  have hgapV : benchmark (density V) < objective V := by rw [hdV, hcV]; exact hgap
  obtain ⟨hclass, _⟩ := fullStationaryClass_of_recorded_rows V hVfull hopt hphysical hdV' hgapV
    m (2 * (c - m * d)) (Eventually.of_forall hVrow)
  rw [hdV, hcV] at hclass
  refine ⟨V, hclass, ?_, hVrow, hphysical⟩
  intro p
  exact ⟨(adjacency_moment_averaged U p).trans (hmom p).1,
    (charge_moment_averaged U p).trans (hmom p).2⟩

/-- Every pointwise boundary-label clique passes the literal conditional
charge test at every finite order. Repeated D labels use independent
fresh conditional samples, without any cardinality hypothesis on atoms. -/
theorem coveredCountableBoundaryCoefficient_tuple_le_one (S : SelectedHighLowStructure W m)
    (mode : Bool) (r a : S.I) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) (hD : 0 < μ S.D)
    (hnull : μ (if mode = true then S.D \ S.rootNeighborhood a
      else S.D ∩ S.rootNeighborhood a) = 0)
    {n : ℕ} (v : Fin n → S.I ⊕ Unit)
    (hv : FiniteArity.TupleClique (S.coveredCountableBoundaryGraph mode r a) v) :
    FiniteArity.tupleCharge S.coveredCountableBoundaryCoefficient v ≤ 1 := by
  let : MeasurableSpace (S.I ⊕ Unit) := ⊤
  let : Countable S.I := S.hI.to_subtype
  let A := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  have hs := (hW.strict_gap_structure hd hgap).strict_support
  have hg : ∀ᵐ p ∂μ.prod μ, A p.1 p.2 =
      S.coveredCountableBoundaryGraph mode r a
        (S.coveredCountableBoundaryLabel p.1) (S.coveredCountableBoundaryLabel p.2) := by
    filter_upwards [S.ae_covered_countable_boundary_graph mode r a hW hd hgap hpair hzero hnull,
      PhysicalRepresentative.adjacency_moment_ae_eq W m hs] with p hp hphys
    have he := hphys.symm.trans hp
    cases hA : A p.1 p.2 <;>
      cases hH : S.coveredCountableBoundaryGraph mode r a
        (S.coveredCountableBoundaryLabel p.1) (S.coveredCountableBoundaryLabel p.2) <;>
      simp_all [A]
  have ht := FiniteArity.conditional_clique_average_le_one
    (fun i : Fin n => S.coveredCountableBoundaryLabel ⁻¹' {v i})
    (fun i => S.measurable_coveredCountableBoundaryLabel (measurableSet_singleton (v i)))
    (fun i => S.coveredCountableBoundaryLabel_fibers_positive hD (v i)) A Y
    (PhysicalRepresentative.measurable_charge W m) 3 (PhysicalRepresentative.charge_bound W m)
    (PhysicalRepresentative.full_feasible W hW.full m hs hW.deterministic n)
    (fun i j hij => hg.mono (fun p hp hx hy => by
      change S.coveredCountableBoundaryLabel p.1 = v i at hx
      change S.coveredCountableBoundaryLabel p.2 = v j at hy
      rw [hp, hx, hy]
      exact hv i j hij))
  have heq : (fun i j : Fin n => if i = j then 0 else
      S.coveredCountableBoundaryCoefficient (v i) (v j)) =
      (fun i j => if i = j then 0 else ∫ p, Y p.1 p.2
        ∂(cond μ (S.coveredCountableBoundaryLabel ⁻¹' {v i})).prod
          (cond μ (S.coveredCountableBoundaryLabel ⁻¹' {v j}))) := by
    funext i j
    by_cases hij : i = j
    · simp [hij]
    · simp only [hij, ite_false, coveredCountableBoundaryCoefficient, FiniteArity.regionPairCharge]
      apply integral_congr_ae
      exact (cond_absolutelyContinuous.prod cond_absolutelyContinuous).ae_le
        ((PhysicalRepresentative.charge_ae_eq W m hs).mono (fun _ h => h.symm))
  change FiniteArity.pairCharge Finset.univ
    (fun i j : Fin n => if i = j then 0 else S.coveredCountableBoundaryCoefficient (v i) (v j)) ≤ 1
  rw [heq]
  exact ht

end Erdos1017.CappedModel.SelectedHighLowStructure
