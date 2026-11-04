module

public import Erdos1017.Exclusions.Common.Physical.PhysicalTriangleExposure
public import Erdos1017.Exclusions.Common.Universal.SelectedUniversalRootDegree
public import Erdos1017.Exclusions.Common.Universal.UniversalCopyInequality

/-!
# Triangle exposure of the selected universal root

The selected model exposes a positive first root star in every singular
pair-`AC` tight triangle law, in every root and leaf coordinate order on one
common triangle-parent event, and the selected optimum constructs its own tight
physical primal with every rooted triangle star positive.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

private theorem ae_all_pairs_of_pair_AC {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {n : ℕ} (ρ : Measure (Fin n → Ω))
    (hpairs : ∀ i j, i ≠ j → ρ.map (fun v => (v i, v j)) ≪ μ.prod μ)
    (P : Ω × Ω → Prop) (hP : ∀ᵐ p ∂μ.prod μ, P p) :
    ∀ᵐ v ∂ρ, ∀ i j, i ≠ j → P (v i, v j) := by
  simp only [ae_all_iff]
  intro i j hij
  exact ae_of_ae_map ((measurable_pi_apply i).prodMk
    (measurable_pi_apply j)).aemeasurable ((hpairs i j hij).ae_le hP)

private theorem ae_all_coordinates_of_pair_AC {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ} (hn : 2 ≤ n)
    (ρ : Measure (Fin n → Ω))
    (hpairs : ∀ i j, i ≠ j → ρ.map (fun v => (v i, v j)) ≪ μ.prod μ)
    (P : Ω → Prop) (hP : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ v ∂ρ, ∀ i, P (v i) := by
  simp only [ae_all_iff]
  intro i
  exact ae_of_ae_map (measurable_pi_apply i).aemeasurable
    ((PhysicalCliqueRepresentative.coordinate_absolutelyContinuous_of_pairs μ hn ρ hpairs i).ae_le hP)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- The actual selected model exposes a positive first root star in every
singular pair-AC tight triangle law. Flat rows, universal fresh sections,
missing capacities and all insertion tests are derived internally. -/
theorem ae_permuted_rooted_triangle_star_pos (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hstar : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → S.ρ p.2 ≠ r.val →
      chargeKernel W p.1 p.2 < 1)
    (hA : 1 / 3 < μ.real {x | S.ρ x = r.val})
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : (1 + m) * (1 - μ.real {x | S.ρ x = r.val}) < 3 * (2 * (c - m * d) + m))
    (ρ : Measure (Fin 3 → Ω)) [IsFiniteMeasure ρ]
    (hpairs : ∀ i j : Fin 3, i ≠ j → ρ.map (fun v => (v i, v j)) ≪ μ.prod μ)
    (hclique : ∀ᵐ v ∂ρ, PhysicalCliqueRepresentative.Clique
      (Function.uncurry (PhysicalRepresentative.adjacency W m)) v)
    (htight : ∀ᵐ v ∂ρ, PhysicalPrimal.charge
      (Function.uncurry (PhysicalRepresentative.charge W m)) v = 1) :
    ∀ᵐ v ∂ρ, ∀ e : Equiv.Perm (Fin 3),
      S.ρ (v (e 0)) = r.val → 0 < S.rootChargeRow r (v (e 1)) := by
  let G := Function.uncurry (PhysicalRepresentative.adjacency W m)
  let Y := Function.uncurry (PhysicalRepresentative.charge W m)
  let I := {x | S.ρ x = r.val}
  have hI : MeasurableSet I := (S.hfibers r.val r.property).1
  have hs := hW.strict_gap_structure hd hgap
  have htest : ∀ n, 2 ≤ n → ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ),
      PhysicalCliqueRepresentative.Clique G v → PhysicalPrimal.charge Y v ≤ 1 := by
    intro n _
    filter_upwards [PhysicalRepresentative.full_feasible W hW.full m hs.strict_support
      hW.deterministic n] with v hv hc
    change PhysicalPrimal.charge (Function.uncurry (PhysicalRepresentative.charge W m)) v ≤ 1
    rw [MultipartiteHeadPrice.physicalCharge_eq_tupleCharge]
    exact hv hc
  have hins := PhysicalTriangleExposure.ae_insertion_le_majorant_permutations G
    (PhysicalRepresentative.measurable_adjacency W m)
    (PhysicalRepresentative.adjacency_symm W m) Y (PhysicalRepresentative.measurable_charge W m)
    (PhysicalRepresentative.charge_symm W m) 3 (by norm_num)
    (fun p => PhysicalRepresentative.charge_bound W m p.1 p.2)
    (fun p => (PhysicalRepresentative.charge_mem_Icc W m p.1 p.2).2)
    (fun p => PhysicalRepresentative.charge_zero_of_nonedge W m p.1 p.2)
    htest (-m) ρ hpairs hclique htight
  have hroot := S.neutral_atom_physical_adjacency r hW hd hgap hN
  have hvertex : ∀ᵐ x ∂μ,
      ((∫ z, Y (z, x) + (-m) * (if G (z, x) then 1 else 0) ∂μ) = 2 * (c - m * d)) ∧
      (S.ρ x = r.val → ∀ᵐ z ∂μ, G (z, x) = false ↔ z ∈ I) ∧
      (S.ρ x ≠ r.val → ∀ᵐ z ∂μ, z ∈ I → G (z, x) = true) ∧
      (S.ρ x ≠ r.val → μ.real {z | G (z, x) = false} ≤ 1 - 2 * μ.real I) := by
    have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hroot
    filter_upwards [S.ae_physical_shifted_column_stationary hW hd hgap,
      Measure.ae_ae_of_ae_prod hroot, Measure.ae_ae_of_ae_prod hswap,
      S.ae_unsaturated_universal_missing_capacity r hW hd hgap hN hstar]
      with x hf hr hc hm
    refine ⟨?_, ?_, ?_, ?_⟩
    · convert hf using 1
      congr 1
      funext z
      cases hg : PhysicalRepresentative.adjacency W m z x <;> simp [G, Y, hg]
      ring
    · intro hx
      filter_upwards [hr] with z hz
      have he := hz hx
      change (PhysicalRepresentative.adjacency W m x z = true ↔ S.ρ z ≠ r.val) at he
      change PhysicalRepresentative.adjacency W m z x = false ↔ S.ρ z = r.val
      rw [PhysicalRepresentative.adjacency_symm W m z x]
      constructor
      · intro hg
        by_contra hne
        have ht := he.mpr hne
        rw [hg] at ht
        contradiction
      · intro hzroot
        cases hg : PhysicalRepresentative.adjacency W m x z with
        | false => rfl
        | true => exact False.elim ((he.mp hg) hzroot)
    · intro hx
      filter_upwards [hc] with z hz hzI
      exact (hz hzI).mpr hx
    · intro hx
      have he : {z | G (z, x) = false} =
          {z | PhysicalRepresentative.adjacency W m x z = false} := by
        ext z
        change PhysicalRepresentative.adjacency W m z x = false ↔
          PhysicalRepresentative.adjacency W m x z = false
        rw [PhysicalRepresentative.adjacency_symm W m z x]
      rw [he]
      exact hm hx
  have hcoords := ae_all_coordinates_of_pair_AC (by norm_num : 2 ≤ 3) ρ hpairs _ hvertex
  have hrootPairs := ae_all_pairs_of_pair_AC ρ hpairs _ hroot
  have hchargePairs := ae_all_pairs_of_pair_AC ρ hpairs _ (S.ae_root_charge r hW hd hgap)
  filter_upwards [hins, hcoords, hrootPairs, hchargePairs, hclique, htight]
    with v hi hc hr hY hv ht e hv0
  have he01 : e 0 ≠ e 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (e.injective h)
  have he02 : e 0 ≠ e 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (e.injective h)
  have hv1 : S.ρ (v (e 1)) ≠ r.val := (hr (e 0) (e 1) he01 hv0).mp (hv _ _ he01)
  have hv2 : S.ρ (v (e 2)) ≠ r.val := (hr (e 0) (e 2) he02 hv0).mp (hv _ _ he02)
  have hold : Y (v (e 0), v (e 1)) + Y (v (e 0), v (e 2)) + Y (v (e 1), v (e 2)) = 1 := by
    have ht' := (PhysicalTriangleExposure.charge_comp_equiv Y v e).trans ht
    have he : (fun i => v (e i)) = ![v (e 0), v (e 1), v (e 2)] := by
      funext i
      fin_cases i <;> rfl
    rw [he, PhysicalTriangleExposure.charge_three Y (PhysicalRepresentative.charge_symm W m)] at ht'
    exact ht'
  have hp := PhysicalTriangleExposure.first_star_pos_of_insertion_and_capacity G
    (PhysicalRepresentative.measurable_adjacency W m) Y (PhysicalRepresentative.measurable_charge W m)
    3 (fun p => PhysicalRepresentative.charge_bound W m p.1 p.2)
    (fun p => (PhysicalRepresentative.charge_mem_Icc W m p.1 p.2).2)
    (-m) (2 * (c - m * d)) ⟨hell.1.le, hell.2.le⟩ (fun i => v (e i)) I hI hA.le
    (by simpa only [sub_neg_eq_add] using hmargin) hold ((hc (e 0)).2.1 hv0)
    ((hc (e 1)).2.2.1 hv1) ((hc (e 2)).2.2.1 hv2) (fun i => (hc (e i)).1)
    ((hc (e 1)).2.2.2 hv1) ((hc (e 2)).2.2.2 hv2) (hi e)
  rw [show Y (v (e 0), v (e 1)) = S.rootChargeRow r (v (e 1)) from hY _ _ he01 hv0] at hp
  exact hp


/-- The first-coordinate form of the same actual selected triangle
exposure, retaining the original singular law. -/
theorem ae_rooted_triangle_star_pos (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hstar : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → S.ρ p.2 ≠ r.val →
      chargeKernel W p.1 p.2 < 1)
    (hA : 1 / 3 < μ.real {x | S.ρ x = r.val})
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : (1 + m) * (1 - μ.real {x | S.ρ x = r.val}) < 3 * (2 * (c - m * d) + m))
    (ρ : Measure (Fin 3 → Ω)) [IsFiniteMeasure ρ]
    (hpairs : ∀ i j : Fin 3, i ≠ j → ρ.map (fun v => (v i, v j)) ≪ μ.prod μ)
    (hclique : ∀ᵐ v ∂ρ, PhysicalCliqueRepresentative.Clique
      (Function.uncurry (PhysicalRepresentative.adjacency W m)) v)
    (htight : ∀ᵐ v ∂ρ, PhysicalPrimal.charge
      (Function.uncurry (PhysicalRepresentative.charge W m)) v = 1) :
    ∀ᵐ v ∂ρ, S.ρ (v 0) = r.val → 0 < S.rootChargeRow r (v 1) := by
  filter_upwards [S.ae_permuted_rooted_triangle_star_pos r hW hd hgap hN hstar hA hell
    hmargin ρ hpairs hclique htight] with v hv
  simpa only [Equiv.refl_apply] using hv (Equiv.refl (Fin 3))

/-- Every original root/leaf coordinate order is exposed on one common
actual triangle-parent event; no permutation symmetry of the law is needed. -/
theorem ae_all_rooted_triangle_stars_pos (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hstar : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → S.ρ p.2 ≠ r.val →
      chargeKernel W p.1 p.2 < 1)
    (hA : 1 / 3 < μ.real {x | S.ρ x = r.val})
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : (1 + m) * (1 - μ.real {x | S.ρ x = r.val}) < 3 * (2 * (c - m * d) + m))
    (ρ : Measure (Fin 3 → Ω)) [IsFiniteMeasure ρ]
    (hpairs : ∀ i j : Fin 3, i ≠ j → ρ.map (fun v => (v i, v j)) ≪ μ.prod μ)
    (hclique : ∀ᵐ v ∂ρ, PhysicalCliqueRepresentative.Clique
      (Function.uncurry (PhysicalRepresentative.adjacency W m)) v)
    (htight : ∀ᵐ v ∂ρ, PhysicalPrimal.charge
      (Function.uncurry (PhysicalRepresentative.charge W m)) v = 1) :
    ∀ᵐ v ∂ρ, ∀ i j : Fin 3, i ≠ j → S.ρ (v i) = r.val →
      0 < S.rootChargeRow r (v j) := by
  have hperm : ∀ i j : Fin 3, i ≠ j → ∃ e : Equiv.Perm (Fin 3), e 0 = i ∧ e 1 = j := by decide
  filter_upwards [S.ae_permuted_rooted_triangle_star_pos r hW hd hgap hN hstar hA hell
    hmargin ρ hpairs hclique htight] with v hv i j hij hi
  obtain ⟨e, he0, he1⟩ := hperm i j hij
  simpa only [he0, he1] using hv e (by simpa only [he0] using hi)

namespace UniversalPhysicalPrimal

variable {S : SelectedHighLowStructure W m} {r : S.I} {d c : ℝ}

/-- Exact physical pair balance supplies all law hypotheses of the actual
triangle exposure. The same original primal may have singular parents. -/
theorem ae_triangle_star_pos (P : S.UniversalPhysicalPrimal r c)
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hstar : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → S.ρ p.2 ≠ r.val →
      chargeKernel W p.1 p.2 < 1)
    (hA : 1 / 3 < μ.real {x | S.ρ x = r.val})
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : (1 + m) * (1 - μ.real {x | S.ρ x = r.val}) < 3 * (2 * (c - m * d) + m)) :
    ∀ᵐ v ∂P.laws 3, ∀ i j : Fin 3, i ≠ j → S.ρ (v i) = r.val →
      0 < S.rootChargeRow r (v j) := by
  have : ∀ n, IsFiniteMeasure (P.laws n) := P.finite
  have hdemand : PhysicalPrimal.graphDemand μ
      {p | PhysicalRepresentative.adjacency W m p.1 p.2 = true} ≪ μ.prod μ :=
    Measure.absolutelyContinuous_restrict
  have hpairs : ∀ i j : Fin 3, i ≠ j →
      (P.laws 3).map (fun v => (v i, v j)) ≪ μ.prod μ := by
    intro i j hij
    exact (PhysicalPrimal.pair_marginal_absolutelyContinuous_of_balance P.laws _
      P.feasible.2.2.2 3 ⟨(i, j), hij⟩).trans hdemand
  exact S.ae_all_rooted_triangle_stars_pos r hW hd hgap hN hstar hA hell hmargin
    (P.laws 3) hpairs (P.feasible.2.2.1 3) (P.tight_physical 3)

end UniversalPhysicalPrimal

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- The original selected optimum constructs its own tight physical
primal and proves every rooted triangle star positive under the stated
unsaturated universal-root scalar gate. No physical law is supplied. -/
theorem exists_universal_physical_triangle_exposure
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hstar : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → S.ρ p.2 ≠ r.val →
      chargeKernel W p.1 p.2 < 1)
    (hA : 1 / 3 < μ.real {x | S.ρ x = r.val})
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : (1 + m) * (1 - μ.real {x | S.ρ x = r.val}) < 3 * (2 * (c - m * d) + m)) :
    ∃ P : S.UniversalPhysicalPrimal r c,
      ∀ᵐ v ∂P.laws 3, ∀ i j : Fin 3, i ≠ j → S.ρ (v i) = r.val →
        0 < S.rootChargeRow r (v j) := by
  obtain ⟨P⟩ := S.exists_universal_physical_primal r hW hd hgap hN
  exact ⟨P, P.ae_triangle_star_pos hW hd hgap hN hstar hA hell hmargin⟩

end Erdos1017.CappedModel.SelectedHighLowStructure
