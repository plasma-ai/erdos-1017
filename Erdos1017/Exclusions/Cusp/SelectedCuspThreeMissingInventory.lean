module

public import Erdos1017.Exclusions.Cusp.SelectedCuspThreeMissingReturn
public import Erdos1017.Exclusions.Cusp.SelectedCuspThreeNeighborhoodTrace
public import Erdos1017.Exclusions.Common.TwoCenter.SelectedTwoCenterFiberPatterns

/-!
# Inventory of the third-cusp missing region

The low missing region has exactly its restricted independent-class square
inventory, and either one atom accounts for at least twenty twenty-firsts of it
or its edge integral pays the dispersed bound; the hole, neighborhood and cross
missing squares are computed on the original law.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

open KernelOperator

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m d c : ℝ}

/-- The original LOW missing region has precisely its restricted original
independent-class square inventory. Dust contributes no missing square. -/
theorem cusp_three_missing_class_inventory (S : SelectedHighLowStructure W m) (i : S.I)
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c)
    (hlow : ∀ᵐ x ∂μ.restrict (S.cuspThreeMissingRegion i), x ∈ S.L) :
    let J := S.cuspThreeMissingRegion i
    let a := fun j : S.I => μ.real (J ∩ {x | S.ρ x = j.val})
    Summable a ∧ Summable (fun j => (a j) ^ 2) ∧
      (∑' j, a j) ≤ μ.real J ∧
      (∑' j, (a j) ^ 2) = (μ.real J) ^ 2 -
        ∫ p in J ×ˢ J, adjacencyKernel W p.1 p.2 ∂μ.prod μ := by
  let : Countable S.I := S.hI.to_subtype
  let : MeasurableSpace (Option S.I) := ⊤
  let J := S.cuspThreeMissingRegion i
  let q : Ω → Option S.I := J.piecewise S.collapsedPartLabel (fun _ => none)
  have hJ := S.measurableSet_cuspThreeMissingRegion i
  have hq : Measurable q := S.measurable_collapsedPartLabel.piecewise hJ measurable_const
  have hf (j : S.I) : q ⁻¹' {some j} = J ∩ {x | S.ρ x = j.val} := by
    ext x
    by_cases hx : x ∈ J
    · simp only [q, Set.piecewise, hx, ite_true, mem_preimage, mem_singleton_iff,
        mem_inter_iff, mem_ofPred_eq, true_and]
      exact Iff.of_eq (congrArg (fun s : Set Ω => x ∈ s) (S.collapsedPartLabel_fiber j))
    · simp [q, hx]
  have hm (j : S.I) : MultipartiteClassMasses.classMass μ q j =
      μ.real (J ∩ {x | S.ρ x = j.val}) := by
    rw [MultipartiteClassMasses.classMass, hf]
  have hsum := MultipartiteClassMasses.classMass_summable (μ := μ) q hq
  have hsquare := MultipartiteClassMasses.classMass_sq_summable (μ := μ) q hq
  change Summable (fun j => MultipartiteClassMasses.classMass μ q j) at hsum
  simp only [hm] at hsum hsquare
  have htotal : (∑' j : S.I, μ.real (J ∩ {x | S.ρ x = j.val})) ≤ μ.real J := by
    have he := MultipartiteClassMasses.tsum_classMass (μ := μ) q hq
    simp only [hm, hf] at he
    rw [he]
    exact measureReal_mono (by
      intro x hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      exact hj.1)
  let Z := MultipartiteClassMasses.independentPairs q
  have hZ := MultipartiteClassMasses.independentPairs_measurable q hq
  have hhalf := S.ae_collapsed_half_support hW hd hgap false
  rw [Measure.prod_restrict] at hhalf
  have hh := (ae_restrict_iff' ((S.measurableSet_half false).prod
    (S.measurableSet_half false))).mp hhalf
  have hl := (ae_restrict_iff' hJ).mp hlow
  have he : (J ×ˢ J).indicator (fun p : Ω × Ω => 1 - adjacencyKernel W p.1 p.2) =ᵐ[μ.prod μ]
      Z.indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [hh, Measure.quasiMeasurePreserving_fst.ae hl,
      Measure.quasiMeasurePreserving_snd.ae hl] with p hp hx hy
    have hz := MultipartiteClassMasses.mem_independentPairs_iff q p
    by_cases hxx : p.1 ∈ J <;> by_cases hyy : p.2 ∈ J
    · have hg := hp ⟨Or.inl (hx hxx), Or.inl (hy hyy)⟩
      change adjacencyKernel W p.1 p.2 = _ at hg
      simp only [q, Set.piecewise, hxx, hyy, ite_true] at hz
      simp only [Set.indicator, mem_prod, hxx, hyy, and_self, ite_true, hg]
      change _ = if p ∈ Z then 1 else 0
      change p ∈ Z ↔ _ at hz
      split_ifs <;> simp_all
    all_goals
      have hn : p ∉ Z := by
        change ¬p ∈ MultipartiteClassMasses.independentPairs q
        rw [MultipartiteClassMasses.mem_independentPairs_iff]
        simp [q, hxx, hyy]
      simp [hxx, hyy, hn]
  have hG : Integrable (fun p : Ω × Ω => adjacencyKernel W p.1 p.2) (μ.prod μ) := by
    simpa only [mul_one] using integrable_kernel_bilinear
      (adjacencyKernel_measurable W) (adjacencyKernel_bound W)
      (integrable_const (1 : ℝ)) (integrable_const (1 : ℝ))
  have hi := integral_congr_ae he
  rw [integral_indicator (hJ.prod hJ), integral_sub (integrable_const 1) hG.integrableOn,
    setIntegral_const, smul_eq_mul, mul_one, measureReal_prod_prod,
    integral_indicator hZ, setIntegral_const, smul_eq_mul, mul_one,
    MultipartiteClassMasses.independentPairs_mass q hq] at hi
  simp only [hm] at hi
  exact ⟨hsum, hsquare, htotal, by simpa only [pow_two] using hi.symm⟩

/-- Either one entire original atom accounts for at least twenty twenty-firsts
of the missing region, or its actual original edge integral pays the dispersed bound. -/
theorem cusp_three_missing_dominant_or_dispersed (S : SelectedHighLowStructure W m) (i : S.I)
    (hdk : d = 4 / 9) (hW : FullStationaryClass d c W m) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hell : -m < 1) (hpeak : S.IsCommonForwardPeak d c i)
    (hnonuniv : ¬(∀ᵐ p ∂μ.prod μ, S.ρ p.1 = i.val →
      adjacencyKernel W p.1 p.2 = if S.ρ p.2 = i.val then 0 else 1)) :
    let J := S.cuspThreeMissingRegion i
    (∃ j : S.I, j ≠ i ∧ (∀ᵐ x ∂μ.restrict {x | S.ρ x = j.val}, x ∈ J) ∧
      μ.real J - S.originalAtomMass j ≤ S.originalAtomMass j / 20) ∨
      (μ.real J) ^ 2 / 42 ≤
        (∫ p in J ×ˢ J, adjacencyKernel W p.1 p.2 ∂μ.prod μ) / 2 := by
  let J := S.cuspThreeMissingRegion i
  let a := fun j : S.I => μ.real (J ∩ {x | S.ρ x = j.val})
  have hJ := S.measurableSet_cuspThreeMissingRegion i
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by norm_num [hdk]
  obtain ⟨ht, hlow, _⟩ :=
    S.cusp_three_low_slope_missing_region i hdk hW hgap hglobal hell hpeak hnonuniv
  obtain ⟨hs, hsq, htotal, hid⟩ :=
    S.cusp_three_missing_class_inventory i hW hd hgap (hlow.mono (fun _ hp => hp.1))
  change Summable a at hs
  change Summable (fun j => (a j) ^ 2) at hsq
  change (∑' j, a j) ≤ μ.real J at htotal
  by_cases hlarge : ∃ j, 20 * μ.real J / 21 ≤ a j
  · obtain ⟨j, hj⟩ := hlarge
    have haj : 0 < a j := lt_of_lt_of_le (by positivity) hj
    have hinside : ∀ᵐ x ∂μ.restrict {x | S.ρ x = j.val}, x ∈ J := by
      rcases S.ae_fiber_missing_or_not j i hW with hin | hout
      · simpa only [← S.cuspThreeMissingRegion_eq_missingSet i] using hin
      · have hout' : ∀ᵐ x ∂μ.restrict {x | S.ρ x = j.val}, x ∉ J := by
          simpa only [← S.cuspThreeMissingRegion_eq_missingSet i] using hout
        have hz : μ (J ∩ {x | S.ρ x = j.val}) = 0 := by
          have he := (ae_iff.mp hout')
          have he' : (μ.restrict {x | S.ρ x = j.val}) J = 0 := by
            simpa only [not_not, Set.ofPred_mem_eq] using he
          rwa [Measure.restrict_apply hJ] at he'
        have ha0 : a j = 0 := by simp [a, measureReal_def, hz]
        exact False.elim (haj.ne' ha0)
    have heq : a j = S.originalAtomMass j := by
      apply measureReal_congr
      filter_upwards [(ae_restrict_iff' (S.hfibers j.val j.property).1).mp hinside]
        with x hx
      simp only [mem_inter_iff, mem_ofPred_eq]
      exact propext ⟨And.right, fun hj => ⟨hx hj, hj⟩⟩
    have hne : j ≠ i := by
      intro hji
      subst j
      obtain ⟨x, hx, hmem⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
        (S.hfibers i.val i.property).2.1.ne' hinside
      exact hmem.1 hx
    exact Or.inl ⟨j, hne, hinside, by rw [heq] at hj; linarith only [hj]⟩
  · right
    have hbound (j : S.I) : (a j) ^ 2 ≤ (20 * μ.real J / 21) * a j := by
      have hlt : a j < 20 * μ.real J / 21 := lt_of_not_ge (fun h => hlarge ⟨j, h⟩)
      have ha : 0 ≤ a j := measureReal_nonneg
      nlinarith only [mul_nonneg ha (sub_nonneg.mpr hlt.le)]
    have hsum := hsq.tsum_le_tsum hbound (hs.mul_left (20 * μ.real J / 21))
    rw [tsum_mul_left] at hsum
    have htotal' := mul_le_mul_of_nonneg_left htotal
      (by positivity : 0 ≤ 20 * μ.real J / 21)
    change (∑' j, (a j) ^ 2) = _ at hid
    nlinarith only [hsum, htotal', hid]

/-- The exact original hole inventory uses the peak, its entire missing
region, and its original neighborhood. No edited model enters this identity. -/
theorem cusp_three_missing_hole_inventory (S : SelectedHighLowStructure W m) (i : S.I)
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) :
    let J := S.cuspThreeMissingRegion i
    let N := S.rootNeighborhood i
    1 - 2 * d = (S.originalAtomMass i + μ.real J) ^ 2 -
      (∫ p in J ×ˢ J, adjacencyKernel W p.1 p.2 ∂μ.prod μ) +
      2 * (∫ p in J ×ˢ N, 1 - adjacencyKernel W p.1 p.2 ∂μ.prod μ) +
      ∫ p in N ×ˢ N, 1 - adjacencyKernel W p.1 p.2 ∂μ.prod μ := by
  let I := {x | S.ρ x = i.val}
  let J := S.cuspThreeMissingRegion i
  let N := S.rootNeighborhood i
  let B := I ∪ J
  let K := fun p : Ω × Ω => 1 - adjacencyKernel W p.1 p.2
  have hI : MeasurableSet I := (S.hfibers i.val i.property).1
  have hJ : MeasurableSet J := S.measurableSet_cuspThreeMissingRegion i
  have hN : MeasurableSet N := S.measurableSet_rootNeighborhood i
  have hB : MeasurableSet B := hI.union hJ
  have hIJ : Disjoint I J := disjoint_left.mpr (fun _ hx hy => hy.1 hx)
  have hIN : Disjoint I N := S.rootNeighborhood_disjoint i
  have hJN : Disjoint J N := disjoint_left.mpr (fun _ hx hy => hx.2 hy)
  have hpart (x : Ω) : x ∈ I ∨ x ∈ J ∨ x ∈ N := by
    by_cases hi : x ∈ I
    · exact Or.inl hi
    · by_cases hn : x ∈ N
      · exact Or.inr (Or.inr hn)
      · exact Or.inr (Or.inl ⟨hi, hn⟩)
  have hG : Integrable (fun p : Ω × Ω => adjacencyKernel W p.1 p.2) (μ.prod μ) := by
    simpa only [mul_one] using integrable_kernel_bilinear
      (adjacencyKernel_measurable W) (adjacencyKernel_bound W)
      (integrable_const (1 : ℝ)) (integrable_const (1 : ℝ))
  have hK : Integrable K (μ.prod μ) := (integrable_const 1).sub hG
  have hBB := (integrable_const (1 : ℝ) (μ := μ.prod μ)).indicator (hB.prod hB)
  have hJJ := hG.indicator (hJ.prod hJ)
  have hJN' := hK.indicator (hJ.prod hN)
  have hNJ := hK.indicator (hN.prod hJ)
  have hNN := hK.indicator (hN.prod hN)
  have he : K =ᵐ[μ.prod μ] fun p =>
      (B ×ˢ B).indicator (fun _ => (1 : ℝ)) p -
        (J ×ˢ J).indicator (fun p => adjacencyKernel W p.1 p.2) p +
        (J ×ˢ N).indicator K p + (N ×ˢ J).indicator K p + (N ×ˢ N).indicator K p := by
    filter_upwards [S.ae_original_root_adjacency i hW hd hgap,
      Measure.measurePreserving_swap.quasiMeasurePreserving.ae
        (S.ae_original_root_adjacency i hW hd hgap), adjacencyKernel_symm W]
      with p hx hy hsym
    have hxnI : p.1 ∈ N → p.1 ∉ I := fun h => disjoint_right.mp hIN h
    have hynI : p.2 ∈ N → p.2 ∉ I := fun h => disjoint_right.mp hIN h
    have hxjI : p.1 ∈ J → p.1 ∉ I := fun h => disjoint_right.mp hIJ h
    have hyjI : p.2 ∈ J → p.2 ∉ I := fun h => disjoint_right.mp hIJ h
    have hxiN : p.1 ∈ I → p.1 ∉ N := fun h => disjoint_left.mp hIN h
    have hyiN : p.2 ∈ I → p.2 ∉ N := fun h => disjoint_left.mp hIN h
    have hxjN : p.1 ∈ J → p.1 ∉ N := fun h => disjoint_left.mp hJN h
    have hyjN : p.2 ∈ J → p.2 ∉ N := fun h => disjoint_left.mp hJN h
    have hxnJ : p.1 ∈ N → p.1 ∉ J := fun h => disjoint_right.mp hJN h
    have hynJ : p.2 ∈ N → p.2 ∉ J := fun h => disjoint_right.mp hJN h
    have hxiJ : p.1 ∈ I → p.1 ∉ J := fun h => disjoint_left.mp hIJ h
    have hyiJ : p.2 ∈ I → p.2 ∉ J := fun h => disjoint_left.mp hIJ h
    rcases hpart p.1 with hxi | hxj | hxn <;> rcases hpart p.2 with hyi | hyj | hyn
    all_goals first
      | have hg := hx hxi
      | have hg := hsym.trans (hy hyi)
      | skip
    all_goals try first
      | change adjacencyKernel W p.1 p.2 = (if p.2 ∈ N then 1 else 0) at hg
      | change adjacencyKernel W p.1 p.2 = (if p.1 ∈ N then 1 else 0) at hg
    all_goals clear hx hy hsym
    all_goals simp_all [B, K]
  have hswap : (∫ p in N ×ˢ J, K p ∂μ.prod μ) =
      ∫ p in J ×ˢ N, K p ∂μ.prod μ := by
    rw [← Measure.prod_restrict, ← Measure.prod_restrict]
    calc
      _ = ∫ p, K (p.2, p.1) ∂(μ.restrict N).prod (μ.restrict J) := by
        apply integral_congr_ae
        filter_upwards [ae_mono (Measure.prod_mono Measure.restrict_le_self
          Measure.restrict_le_self) (adjacencyKernel_symm W)] with p hp
        exact congrArg (fun x : ℝ => 1 - x) hp
      _ = _ := integral_prod_swap K
  have hi := integral_congr_ae he
  have ha1 := integral_add (((hBB.sub hJJ).add hJN').add hNJ) hNN
  have ha2 := integral_add ((hBB.sub hJJ).add hJN') hNJ
  have ha3 := integral_add (hBB.sub hJJ) hJN'
  have ha4 := integral_sub hBB hJJ
  simp only [Pi.add_apply, Pi.sub_apply] at ha1 ha2 ha3 ha4
  rw [ha1, ha2, ha3, ha4,
    integral_indicator (hB.prod hB), setIntegral_const, smul_eq_mul, mul_one,
    measureReal_prod_prod, integral_indicator (hJ.prod hJ),
    integral_indicator (hJ.prod hN), integral_indicator (hN.prod hJ),
    integral_indicator (hN.prod hN), hswap] at hi
  have hmass : μ.real B = μ.real I + μ.real J := measureReal_union hIJ hJ
  have htotal : (∫ p, K p ∂μ.prod μ) = 1 - 2 * d := by
    rw [integral_sub (integrable_const 1) hG, integral_const, probReal_univ,
      smul_eq_mul, mul_one]
    have he := hW.density_eq
    unfold density at he
    change (∫ p : Ω × Ω, adjacencyKernel W p.1 p.2 ∂μ.prod μ) / 2 = d at he
    change _ = 1 - 2 * d
    linarith only [he]
  rw [htotal, hmass] at hi
  change 1 - 2 * d = (μ.real I + μ.real J) ^ 2 - _ + 2 * _ + _
  nlinarith only [hi]

/-- The original neighborhood missing integral is the literal physical
missing-body square used by the copy trace. -/
theorem cusp_three_neighborhood_missing_square (S : SelectedHighLowStructure W m) (i : S.I)
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) :
    (∫ p in S.rootNeighborhood i ×ˢ S.rootNeighborhood i,
      1 - adjacencyKernel W p.1 p.2 ∂μ.prod μ) =
      ∫ p : Ω × Ω, (IndependentAtomCopy.missingBody (PhysicalRepresentative.adjacency W m)
        (S.rootNeighborhood i)ᶜ p.1 p.2) ^ 2 ∂μ.prod μ := by
  rw [← integral_indicator ((S.measurableSet_rootNeighborhood i).prod
    (S.measurableSet_rootNeighborhood i))]
  apply integral_congr_ae
  filter_upwards [PhysicalRepresentative.adjacency_moment_ae_eq W m
    (hW.strict_gap_structure hd hgap).strict_support] with p hp
  change adjacencyKernel W p.1 p.2 = _ at hp
  by_cases hx : p.1 ∈ S.rootNeighborhood i <;>
    by_cases hy : p.2 ∈ S.rootNeighborhood i <;>
    cases hg : PhysicalRepresentative.adjacency W m p.1 p.2 <;>
    simp [hx, hy, IndependentAtomCopy.missingBody, hp, hg]

/-- The mixed missing inventory is also its physical indicator-square
integral, on the same original product law. -/
theorem cusp_three_cross_missing_square (S : SelectedHighLowStructure W m) (i : S.I)
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) :
    (∫ p in S.cuspThreeMissingRegion i ×ˢ S.rootNeighborhood i,
      1 - adjacencyKernel W p.1 p.2 ∂μ.prod μ) =
      ∫ p : Ω × Ω, ((S.cuspThreeMissingRegion i ×ˢ S.rootNeighborhood i).indicator
        (fun p => if PhysicalRepresentative.adjacency W m p.1 p.2 then (0 : ℝ) else 1) p) ^ 2
        ∂μ.prod μ := by
  rw [← integral_indicator ((S.measurableSet_cuspThreeMissingRegion i).prod
    (S.measurableSet_rootNeighborhood i))]
  apply integral_congr_ae
  filter_upwards [PhysicalRepresentative.adjacency_moment_ae_eq W m
    (hW.strict_gap_structure hd hgap).strict_support] with p hp
  change adjacencyKernel W p.1 p.2 = _ at hp
  by_cases hx : p.1 ∈ S.cuspThreeMissingRegion i <;>
    by_cases hy : p.2 ∈ S.rootNeighborhood i <;>
    cases hg : PhysicalRepresentative.adjacency W m p.1 p.2 <;>
    simp [hx, hy, hp, hg]

/-- The dispersed original missing region pays a strict improvement in the
neighborhood hole bound through its actual density-return inequality. -/
theorem cusp_three_dispersed_missing_bound (S : SelectedHighLowStructure W m) (i : S.I)
    (hdk : d = 4 / 9) (hW : FullStationaryClass d c W m) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hell : -m < 1) (hpeak : S.IsCommonForwardPeak d c i)
    (hnonuniv : ¬(∀ᵐ p ∂μ.prod μ, S.ρ p.1 = i.val →
      adjacencyKernel W p.1 p.2 = if S.ρ p.2 = i.val then 0 else 1))
    (hdispersed : (μ.real (S.cuspThreeMissingRegion i)) ^ 2 / 42 ≤
      (∫ p in S.cuspThreeMissingRegion i ×ˢ S.cuspThreeMissingRegion i,
        adjacencyKernel W p.1 p.2 ∂μ.prod μ) / 2) :
    let A := S.originalAtomMass i
    let t := μ.real (S.cuspThreeMissingRegion i)
    (∫ p : Ω × Ω, (IndependentAtomCopy.missingBody (PhysicalRepresentative.adjacency W m)
      (S.rootNeighborhood i)ᶜ p.1 p.2) ^ 2 ∂μ.prod μ) <
        1 / 9 - (A + t) ^ 2 - t * (A + t) / 21 := by
  let A := S.originalAtomMass i
  let J := S.cuspThreeMissingRegion i
  let t := μ.real J
  let z := (∫ p in J ×ˢ J, adjacencyKernel W p.1 p.2 ∂μ.prod μ) / 2
  let v := ∫ p in J ×ˢ S.rootNeighborhood i, 1 - adjacencyKernel W p.1 p.2 ∂μ.prod μ
  let H := ∫ p : Ω × Ω, (IndependentAtomCopy.missingBody
    (PhysicalRepresentative.adjacency W m) (S.rootNeighborhood i)ᶜ p.1 p.2) ^ 2 ∂μ.prod μ
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := by norm_num [hdk]
  have hA : 0 < A :=
    ENNReal.toReal_pos (S.hfibers i.val i.property).2.1.ne' (measure_ne_top μ _)
  obtain ⟨ht, _⟩ :=
    S.cusp_three_low_slope_missing_region i hdk hW hgap hglobal hell hpeak hnonuniv
  change 0 < t at ht
  change t ^ 2 / 42 ≤ z at hdispersed
  have hz : 0 < z := lt_of_lt_of_le (div_pos (sq_pos_of_pos ht) (by norm_num)) hdispersed
  have hreturn := (S.cusp_three_missing_return i hdk hW hgap hglobal hell hpeak hnonuniv).2.2.2.1 hz
  change 0 < _ ∧ (2 + A / t) * z < v at hreturn
  have hret := mul_lt_mul_of_pos_right hreturn.2 ht
  have hdiv : (A / t) * t = A := div_mul_cancel₀ A ht.ne'
  have hret' : (2 * t + A) * z < v * t := by
    nlinarith only [hret, congrArg (fun x : ℝ => x * z) hdiv]
  have hhole := S.cusp_three_missing_hole_inventory i hW hd hgap
  dsimp only at hhole
  rw [S.cusp_three_neighborhood_missing_square i hW hd hgap] at hhole
  change 1 - 2 * d = (A + t) ^ 2 - _ + 2 * v + H at hhole
  have hhole' : 1 / 9 = (A + t) ^ 2 - 2 * z + 2 * v + H := by
    dsimp [z]
    rw [hdk] at hhole
    linarith only [hhole]
  have hpaid := mul_nonneg (show 0 ≤ A + t by positivity)
    (sub_nonneg.mpr hdispersed)
  change H < 1 / 9 - (A + t) ^ 2 - t * (A + t) / 21
  have hstrict : t * H < t * (1 / 9 - (A + t) ^ 2 - t * (A + t) / 21) := by
    nlinarith only [hret', hpaid, congrArg (fun x : ℝ => t * x) hhole']
  exact (mul_lt_mul_iff_right₀ ht).mp hstrict

/-- The numerical mass threshold used by the dispersed scalar exit remains
an explicit hypothesis; all hole and return inputs are derived. -/
theorem cusp_three_dispersed_missing_bound_of_mass (S : SelectedHighLowStructure W m) (i : S.I)
    (hdk : d = 4 / 9) (hW : FullStationaryClass d c W m) (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hell : -m < 1) (hpeak : S.IsCommonForwardPeak d c i)
    (hnonuniv : ¬(∀ᵐ p ∂μ.prod μ, S.ρ p.1 = i.val →
      adjacencyKernel W p.1 p.2 = if S.ρ p.2 = i.val then 0 else 1))
    (hdispersed : (μ.real (S.cuspThreeMissingRegion i)) ^ 2 / 42 ≤
      (∫ p in S.cuspThreeMissingRegion i ×ˢ S.cuspThreeMissingRegion i,
        adjacencyKernel W p.1 p.2 ∂μ.prod μ) / 2)
    (hmass : 1 / 27 ≤ μ.real (S.cuspThreeMissingRegion i)) :
    let B := S.originalAtomMass i + μ.real (S.cuspThreeMissingRegion i)
    (∫ p : Ω × Ω, (IndependentAtomCopy.missingBody (PhysicalRepresentative.adjacency W m)
      (S.rootNeighborhood i)ᶜ p.1 p.2) ^ 2 ∂μ.prod μ) ≤ 1 / 9 - B ^ 2 - B / 567 := by
  have hstrict := S.cusp_three_dispersed_missing_bound i hdk hW hgap hglobal hell hpeak
    hnonuniv hdispersed
  have hB : 0 ≤ S.originalAtomMass i + μ.real (S.cuspThreeMissingRegion i) := by
    exact add_nonneg measureReal_nonneg measureReal_nonneg
  dsimp only at hstrict ⊢
  nlinarith only [hstrict, mul_nonneg hB (sub_nonneg.mpr hmass)]

end Erdos1017.CappedModel.SelectedHighLowStructure
