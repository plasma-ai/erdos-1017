module

public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredRepeatWitness
public import Erdos1017.Exclusions.Common.HomogeneousCompletionWitness

/-!
# Completion violations of independent sets

Every measurable positive independent set in a full stationary optimum has a
finite positive-measure completion violation at the optimum's own neutral
shifted charge, and a labeled active optimum has a same-model two-copy witness.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- Every measurable positive independent set in this full stationary
optimum has a finite positive-measure completion violation at its own
neutral shifted charge. No selected labels or new model are assumed. -/
theorem exists_positive_completion_violation_of_independent
    (W : Model Ω μ) {m d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (D : Set Ω) [DecidablePred (· ∈ D)] (hD : MeasurableSet D) (hpos : 0 < μ D)
    (hind : ∀ᵐ p ∂(μ.restrict D).prod (μ.restrict D), adjacencyKernel W p.1 p.2 = 0) :
    ∃ n, 2 ≤ n ∧ 0 < (Measure.pi (fun _ : Fin n => μ))
      {v | FiniteArity.TupleClique
          (FiniteArity.completeAdjacency (PhysicalRepresentative.adjacency W m) D) v ∧
        1 < FiniteArity.tupleCharge
          (FiniteArity.completeCharge (PhysicalRepresentative.adjacency W m)
            (PhysicalRepresentative.charge W m) D (-m)) v} := by
  have hs := hW.strict_gap_structure hd hgap
  apply FiniteArity.exists_positive_violation_of_not_all_feasible μ
  intro hcap
  obtain ⟨v, hL, hQ⟩ := hW.exists_transverse_positive_direction hd hgap
  have hopt : objective W = FractionalGraph.densityLimit (density W) := by
    rw [hW.objective_eq, hW.density_eq]
    exact hW.optimal
  have hmass := ZeroCompletion.missingMass_eq_zero_of_full_optimum W hopt m
    (2 * (c - m * d)) hW.multiplier_mem hs.strict_support hW.stationary
    v hL hQ D hD hcap
  have hcomplete := ZeroCompletion.ae_complete_of_missingMass_eq_zero W m D hD
    hs.strict_support hmass
  rw [Measure.prod_restrict] at hind
  have hind' := (ae_restrict_iff' (hD.prod hD)).mp hind
  have hfalse : ∀ᵐ p ∂μ.prod μ, p.1 ∈ D → p.2 ∈ D → False := by
    filter_upwards [hcomplete, hind'] with p hc hi hx hy
    have he := hc hx hy
    have hz := hi ⟨hx, hy⟩
    change W.moment CappedColor.adjacency p = 0 at hz
    linarith
  obtain ⟨x, hx, hrow⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos.ne'
    (ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hfalse))
  obtain ⟨y, hy, hxy⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos.ne'
    (ae_restrict_of_ae hrow)
  exact hxy hx hy

/-- The same-model generic witness bridge for a labeled active optimum.
Original row and support geometry are explicit; selected labels, repeat
tests, and any claim that the model was reselected are absent. -/
theorem exists_two_copy_witness_of_independent
    (W : Model Ω μ) {m d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (R D : Set Ω) [DecidablePred (· ∈ D)] (hdisj : Disjoint R D)
    (hD : MeasurableSet D) (hpos : 0 < μ D)
    (hind : ∀ᵐ p ∂(μ.restrict D).prod (μ.restrict D), adjacencyKernel W p.1 p.2 = 0)
    (hroot : ∀ᵐ p ∂μ.prod μ, p.1 ∈ R → p.2 ∈ R → adjacencyKernel W p.1 p.2 = 0)
    (hbody : ∀ᵐ p ∂μ.prod μ, p.1 ∉ R → p.2 ∉ R → chargeKernel W p.1 p.2 ≤ 0)
    (w : Ω → ℝ) (hrow : ∀ᵐ p ∂μ.prod μ, p.1 ∈ D → chargeKernel W p.1 p.2 = w p.2)
    (hell : 1 / 2 < -m) (Good : ∀ n, (Fin n → Ω) → Prop)
    (hGood : ∀ n, ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ), Good n v) :
    ∃ n, 2 ≤ n ∧ ∃ v : Fin n → Ω,
      FiniteArity.TupleClique
        (FiniteArity.completeAdjacency (PhysicalRepresentative.adjacency W m) D) v ∧
      Good n v ∧ ∃ T : Finset (Fin n), T ⊆ Finset.univ.filter (fun i => v i ∈ D) ∧
        T.card = 2 ∧ 1 < FiniteArity.pairCharge (T ∪ Finset.univ.filter (fun i => v i ∉ D))
          (fun i j => if i = j then 0 else FiniteArity.completeCharge
            (PhysicalRepresentative.adjacency W m) (PhysicalRepresentative.charge W m)
            D (-m) (v i) (v j)) ∧
        -m < ∑ i ∈ Finset.univ.filter (fun i => v i ∉ D), w (v i) := by
  have hs := hW.strict_gap_structure hd hgap
  have hind' := hind
  rw [Measure.prod_restrict] at hind'
  have hcell := (ae_restrict_iff' (hD.prod hD)).mp hind'
  have hphysical : ∀ᵐ p ∂μ.prod μ,
      (p.1 ∈ R → p.2 ∈ R → PhysicalRepresentative.adjacency W m p.1 p.2 = false) ∧
      (p.1 ∈ D → p.2 ∈ D → PhysicalRepresentative.adjacency W m p.1 p.2 = false) ∧
      (p.1 ∉ R → p.2 ∉ R → PhysicalRepresentative.charge W m p.1 p.2 ≤ 0) ∧
      (p.1 ∈ D → PhysicalRepresentative.charge W m p.1 p.2 = w p.2) := by
    filter_upwards [hroot, hcell, hbody, hrow,
      PhysicalRepresentative.adjacency_moment_ae_eq W m hs.strict_support,
      PhysicalRepresentative.charge_ae_eq W m hs.strict_support] with p hr hc hb hw hG hY
    have hzero (hz : adjacencyKernel W p.1 p.2 = 0) :
        PhysicalRepresentative.adjacency W m p.1 p.2 = false := by
      change W.moment CappedColor.adjacency p = 0 at hz
      rw [hz] at hG
      cases hA : PhysicalRepresentative.adjacency W m p.1 p.2
      · rfl
      · simp only [hA, ite_true] at hG
        norm_num at hG
    exact ⟨fun hx hy => hzero (hr hx hy), fun hx hy => hzero (hc ⟨hx, hy⟩),
      fun hx hy => hY.trans_le (hb hx hy), fun hx => hY.trans (hw hx)⟩
  obtain ⟨n, hn, hpositive⟩ := exists_positive_completion_violation_of_independent W hW hd hgap
    D hD hpos hind
  have hgood := FiniteArity.ae_two_copy_subset_of_homogeneous_completion μ
    (PhysicalRepresentative.adjacency W m) (PhysicalRepresentative.charge W m)
    (PhysicalRepresentative.adjacency_symm W m) (PhysicalRepresentative.charge_symm W m)
    (fun x y => (PhysicalRepresentative.charge_mem_Icc W m x y).2)
    R D hdisj (-m) hell w (hphysical.mono (fun _ h => h.1))
    (hphysical.mono (fun _ h => h.2.1)) (hphysical.mono (fun _ h => h.2.2.1))
    (hphysical.mono (fun _ h => h.2.2.2))
    (PhysicalRepresentative.full_feasible W hW.full m hs.strict_support hW.deterministic) n
  obtain ⟨v, hv, htest⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpositive.ne'
    (ae_restrict_of_ae (hgood.and (hGood n)))
  obtain ⟨T, hTD, hcard, hbad, hincidence⟩ := htest.1 hv.1 hv.2
  exact ⟨n, hn, v, hv.1, htest.2, T, hTD, hcard, hbad, hincidence⟩

end Erdos1017.CappedModel
