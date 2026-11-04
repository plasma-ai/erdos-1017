module

public import Erdos1017.Exclusions.Common.SelectedAtomicChargeBlocks
public import Erdos1017.Exclusions.Common.SelectedRepeatDiffuseContext

/-!
# Atoms when the diffuse region is null

A null diffuse region `D` removes the diffuse point from the repeat witness,
leaving the bare-root threshold, so at most one exterior atom survives and the
atoms are covered by three labels: the root, its saturated head and at most one
other atom.
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

/-- Null D removes the diffuse point from the original actual repeat
witness. The retained common vertex/pair events give the literal atomic
bare-root threshold without any boundary averaging or positive-D premise. -/
theorem covered_null_diffuse_bare_repeat (S : SelectedHighLowStructure W m) (r u : S.I)
    (hru : r ≠ u) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : 1 / 2 < -m)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) (hDnull : μ S.D = 0)
    (hratio : μ.real {x | S.ρ x = r.val} * (1 + m) < 2 * (2 * (c - m * d) + m)) :
    -m < 2 * S.coveredCountableBoundaryCoefficient (Sum.inl r) (Sum.inl u) - 1 := by
  let A := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  let P : Ω × Ω → Prop := fun p =>
    (S.ρ p.1 = r.val → S.ρ p.2 = r.val → A p.1 p.2 = false) ∧
    (S.ρ p.1 = u.val → S.ρ p.2 = u.val → A p.1 p.2 = false) ∧
    (S.ρ p.1 = u.val → Y p.1 p.2 = S.rootChargeRow u p.2)
  have hP : ∀ᵐ p ∂μ.prod μ, P p :=
    (S.ae_root_fiber_physical_independent r hW hd hgap).and
      ((S.ae_root_fiber_physical_independent u hW hd hgap).and (S.ae_root_charge u hW hd hgap))
  let Vx := fun x : Ω => x ∉ S.D ∧ (S.ρ x = r.val → S.rootChargeRow u x =
    S.coveredCountableBoundaryCoefficient (Sum.inl u) (Sum.inl r))
  have hVx : ∀ᵐ x ∂μ, Vx x := (measure_eq_zero_iff_ae_notMem.mp hDnull).and
    ((ae_restrict_iff' (S.hfibers r.val r.property).1).mp
      (S.ae_atomic_rootChargeRow u r hW hd hgap))
  let Good : ∀ n, (Fin n → Ω) → Prop := fun _ cfg =>
    (∀ i j, i ≠ j → P (cfg i, cfg j)) ∧ ∀ i, Vx (cfg i)
  have hGood (n : ℕ) : ∀ᵐ cfg ∂Measure.pi (fun _ : Fin n => μ), Good n cfg := by
    have hv : ∀ᵐ cfg ∂Measure.pi (fun _ : Fin n => μ), ∀ i, Vx (cfg i) := by
      apply ae_all_iff.mpr
      intro i
      exact (measurePreserving_eval (fun _ : Fin n => μ) i).quasiMeasurePreserving.ae hVx
    exact (FiniteArity.ae_all_pairs μ n P hP).and hv
  obtain ⟨n, _, cfg, hclique, hgood, T, hTC, hcard, hbad, _, ⟨b, hb, hbR⟩, _, hclasses⟩ :=
    S.exists_root_diffuse_completion_witness r u hru hW hd hgap hell hzero hratio Good hGood
  let E := Finset.univ.filter (fun i : Fin n => cfg i ∉ {x | S.ρ x = u.val})
  let Z := fun i j : Fin n => if i = j then 0 else
    FiniteArity.completeCharge A Y {x | S.ρ x = u.val} (-m) (cfg i) (cfg j)
  let t := S.coveredCountableBoundaryCoefficient (Sum.inl u) (Sum.inl r)
  have hE (i : Fin n) (hi : i ∈ E) : S.ρ (cfg i) ≠ u.val := (Finset.mem_filter.mp hi).2
  have hT (i : Fin n) (hi : i ∈ T) : S.ρ (cfg i) = u.val := (Finset.mem_filter.mp (hTC hi)).2
  have hroot (i : Fin n) (hi : i ∈ E) : S.ρ (cfg i) = r.val :=
    (hclasses i hi).resolve_right (hgood.2 i).1
  have hEeq : E = {b} := by
    ext i
    constructor
    · intro hi
      apply Finset.mem_singleton.mpr
      by_contra hib
      have hz := (hgood.1 i b hib).1 (hroot i hi) hbR
      have hDD : ¬(cfg i ∈ {x | S.ρ x = u.val} ∧ cfg b ∈ {x | S.ρ x = u.val}) :=
        fun h => hE i hi h.1
      have hc : A (cfg i) (cfg b) = true := by
        simpa only [FiniteArity.completeAdjacency, ite_eq_right hDD] using hclique i b hib
      rw [hc] at hz
      contradiction
    · intro hi
      exact (Finset.mem_singleton.mp hi) ▸ hb
  have hdiag (i : Fin n) : Z i i = 0 := by simp [Z]
  have hsym (i j : Fin n) : Z i j = Z j i := by
    by_cases hij : i = j
    · simp [Z, hij]
    · simp only [Z, hij, Ne.symm hij, ite_false, FiniteArity.completeCharge,
        PhysicalRepresentative.adjacency_symm W m (cfg i) (cfg j),
        PhysicalRepresentative.charge_symm W m (cfg i) (cfg j), A, Y]
      congr 1
      exact propext (by tauto)
  have hdisj : Disjoint T E := by
    apply Finset.disjoint_left.mpr
    exact fun i hi he => hE i he (hT i hi)
  have hcell (i : Fin n) (hi : i ∈ T) (j : Fin n) (hj : j ∈ T) (hij : i ≠ j) :
      Z i j = -(-m) := by
    have hz := (hgood.1 i j hij).2.1 (hT i hi) (hT j hj)
    simp [Z, hij, FiniteArity.completeCharge, hT i hi, hT j hj, hz]
  have hrow (i : Fin n) (hi : i ∈ T) (j : Fin n) (hj : j ∈ E) : Z i j = t := by
    have hij : i ≠ j := fun he => hE j hj (he ▸ hT i hi)
    simp only [Z, hij, ite_false, FiniteArity.completeCharge, Set.mem_ofPred_eq,
      hE j hj, and_false, false_and, ite_false]
    exact ((hgood.1 i j hij).2.2 (hT i hi)).trans ((hgood.2 j).2 (hroot j hj))
  have hformula := FiniteArity.pairCharge_homogeneous_cell T E hdisj Z hdiag hsym (-m)
    (fun _ => t) hcell hrow
  change 1 < FiniteArity.pairCharge (T ∪ E) Z at hbad
  rw [hformula, hcard, hEeq] at hbad
  have hsingle : FiniteArity.pairCharge {b} Z = 0 := by
    simp [FiniteArity.pairCharge, FiniteArity.crossSum, hdiag]
  rw [hsingle] at hbad
  simp only [Finset.sum_singleton, Nat.cast_ofNat] at hbad
  have ht : -m < 2 * t - 1 := by linarith
  simpa only [t, S.coveredCountableBoundaryCoefficient_symm (Sum.inl u) (Sum.inl r)] using ht

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- At most one exterior atom survives when the genuine diffuse region
is null. Both repeat thresholds and the actual joint rooted test are derived. -/
theorem covered_null_diffuse_exterior_unique (S : SelectedHighLowStructure W m) (r a u v : S.I)
    (hru : r ≠ u) (hau : a ≠ u) (hrv : r ≠ v) (hav : a ≠ v)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a) (hell : 1 / 2 < -m)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) (hDnull : μ S.D = 0)
    (hratio : μ.real {x | S.ρ x = r.val} * (1 + m) < 2 * (2 * (c - m * d) + m)) : u = v := by
  by_contra huv
  have hu := S.covered_null_diffuse_bare_repeat r u hru hW hd hgap hell hzero hDnull hratio
  have hv := S.covered_null_diffuse_bare_repeat r v hrv hW hd hgap hell hzero hDnull hratio
  obtain ⟨htri, hfloor⟩ := S.exterior_atomic_triangle_and_floor r a u v hru hau hrv hav huv
    hW hd hgap hpair hzero
  linarith

/-- A null diffuse region leaves the root, its saturated head, and at most
one other original atom. The chosen third label may be the saturated head. -/
theorem exists_covered_null_diffuse_three_label_cover (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a) (hell : 1 / 2 < -m)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) (hDnull : μ S.D = 0)
    (hratio : μ.real {x | S.ρ x = r.val} * (1 + m) < 2 * (2 * (c - m * d) + m)) :
    ∃ z : S.I, r ≠ z ∧ ∀ u : S.I, u = r ∨ u = a ∨ u = z := by
  by_cases hex : ∃ z : S.I, z ≠ r ∧ z ≠ a
  · obtain ⟨z, hzr, hza⟩ := hex
    refine ⟨z, Ne.symm hzr, ?_⟩
    intro u
    by_cases hur : u = r
    · exact Or.inl hur
    by_cases hua : u = a
    · exact Or.inr (Or.inl hua)
    exact Or.inr (Or.inr (S.covered_null_diffuse_exterior_unique r a u z
      (Ne.symm hur) (Ne.symm hua) (Ne.symm hzr) (Ne.symm hza) hW hd hgap hpair
      hell hzero hDnull hratio))
  · refine ⟨a, hpair.1, ?_⟩
    intro u
    by_cases hur : u = r
    · exact Or.inl hur
    have hua : u = a := by by_contra hn; exact hex ⟨u, hur, hn⟩
    exact Or.inr (Or.inl hua)

end Erdos1017.CappedModel.SelectedHighLowStructure
