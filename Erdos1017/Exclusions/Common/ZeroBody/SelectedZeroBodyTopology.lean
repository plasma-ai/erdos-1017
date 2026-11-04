module

public import Erdos1017.Exclusions.Common.ZeroBody.SelectedZeroBodyAtomFloor
public import Erdos1017.Exclusions.Common.ZeroBody.SelectedZeroBodyRows
public import Erdos1017.Exclusions.Common.NeutralNeighborhoodExchange
public import Erdos1017.Exclusions.Common.RetainedRowStationarity
public import Erdos1017.SelectedModel.ZeroClass.AtomlessClassLabels
public import Erdos1017.Exclusions.Common.SelectedDiffuseIncidence

/-!
# Adjacency of exterior atoms in the zero-body branch

In the zero-body strict-gap model an exterior atom cannot miss positive diffuse
mass joined to the saturated head, so every exterior independent whole atom sees
the diffuse neighborhood of its saturated head, as an original adjacency
statement.
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

omit [MeasurableEq Ω] [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem exists_piece_and_positive_remainder
    (T : Set Ω) (hT : MeasurableSet T) (hpos : 0 < μ T)
    (ε : ℝ) (hε : 0 < ε) (hεT : ε < μ.real T) :
    ∃ K U : Set Ω, K ⊆ T ∧ U ⊆ T ∧ MeasurableSet K ∧ MeasurableSet U ∧
      Disjoint K U ∧ μ.real K = ε ∧ 0 < μ K ∧ 0 < μ U := by
  let a := μ.real T
  have ha : 0 < a := ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
  let t := ε / a
  have ht : 0 < t := div_pos hε ha
  have ht1 : t < 1 := (div_lt_one ha).mpr hεT
  let w : Fin 2 → ℝ := ![t, 1 - t]
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    fin_cases i
    · exact ht.le
    · exact sub_nonneg.mpr ht1.le
  have hsum : ∑ i, w i = 1 := by simp [w, Fin.sum_univ_two]
  obtain ⟨L, hL, hmass⟩ := exists_atomless_class_labels_of_masses T hT hpos
    (by decide : 0 < 2) w hw hsum
  let K := T ∩ L ⁻¹' {0}
  let U := T ∩ L ⁻¹' {1}
  have hKmass : μ.real K = ε := by
    rw [hmass]
    change a * (ε / a) = ε
    field_simp
  have hUmass : 0 < μ.real U := by
    rw [hmass]
    exact mul_pos ha (sub_pos.mpr ht1)
  refine ⟨K, U, inter_subset_left, inter_subset_left,
    hT.inter (hL.measurable (measurableSet_singleton 0)),
    hT.inter (hL.measurable (measurableSet_singleton 1)), ?_, hKmass, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    intro x hx hy
    have h0 : L x = 0 := hx.2
    have h1 : L x = 1 := hy.2
    have hf : (0 : Fin 2) = 1 := h0.symm.trans h1
    norm_num at hf
  · by_contra hn
    have hz : μ K = 0 := le_antisymm (le_of_not_gt hn) bot_le
    have he : μ.real K = 0 := by simp [Measure.real, hz]
    linarith
  · by_contra hn
    have hz : μ U = 0 := le_antisymm (le_of_not_gt hn) bot_le
    have he : μ.real U = 0 := by simp [Measure.real, hz]
    linarith

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem ae_fiber_moment_rows
    (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m) :
    ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val},
      (∫ y, adjacencyKernel W x y ∂μ) = wholeRowDegree r.val ∧
      (∫ y, chargeKernel W x y ∂μ) = 2 * (c - m * d) + m * wholeRowDegree r.val := by
  have hY : Integrable (fun p : Ω × Ω => chargeKernel W p.1 p.2) (μ.prod μ) :=
    Integrable.of_bound (chargeKernel_measurable W) 3 (chargeKernel_bound W)
  have hG : Integrable (fun p : Ω × Ω => adjacencyKernel W p.1 p.2) (μ.prod μ) :=
    Integrable.of_bound (adjacencyKernel_measurable W) 1 (adjacencyKernel_bound W)
  filter_upwards [(S.hfibers r.val r.property).2.2.2.rows,
    ae_restrict_of_ae hW.stationary, ae_restrict_of_ae hY.prod_right_ae,
    ae_restrict_of_ae hG.prod_right_ae] with x hx hstat hy hg
  have hdeg : (∫ y, adjacencyKernel W x y ∂μ) = wholeRowDegree r.val :=
    integral_congr_ae hx.2.1
  refine ⟨hdeg, ?_⟩
  have he : (fun y => shiftedKernel W m x y) =
      fun y => chargeKernel W x y - m * adjacencyKernel W x y := by
    funext y
    exact shiftedMoment_eq W m (x, y)
  rw [he, integral_sub hy (hg.const_mul m), integral_const_mul, hdeg] at hstat
  linarith

private theorem degree_ne_of_missing_fibers
    (S : SelectedHighLowStructure W m) (a u : S.I) (hau : a ≠ u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hzero : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = a.val → S.ρ p.2 = u.val →
      adjacencyKernel W p.1 p.2 = 0) : wholeRowDegree a.val ≠ wholeRowDegree u.val := by
  let A := {x | S.ρ x = a.val}
  let U := {x | S.ρ x = u.val}
  have hA : MeasurableSet A := (S.hfibers a.val a.property).1
  have hU : MeasurableSet U := (S.hfibers u.val u.property).1
  have hG0 : ∀ᵐ p ∂(μ.restrict A).prod (μ.restrict U), adjacencyKernel W p.1 p.2 = 0 := by
    rw [Measure.prod_restrict]
    apply (ae_restrict_iff' (hA.prod hU)).mpr
    exact hzero.mono (fun _ h hp => h hp.1 hp.2)
  have hM0 := shiftedKernel_zero_of_adjacency_zero W m hW.moment_mem
    (hW.strict_gap_structure hd hgap).strict_support A U hG0
  have hle : (μ.restrict A).prod (μ.restrict U) ≤ μ.prod μ :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  have hgood : ∀ᵐ p ∂(μ.restrict A).prod (μ.restrict U), wholeRowDegree a.val ≠ wholeRowDegree u.val := by
    filter_upwards [hM0, ae_mono hle S.hdegreeNe,
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hA),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hU),
      Measure.quasiMeasurePreserving_fst.ae (wholeRowFiber_degree W m S.ρ a.val
        (S.hfibers a.val a.property).2.2.2),
      Measure.quasiMeasurePreserving_snd.ae (wholeRowFiber_degree W m S.ρ u.val
        (S.hfibers u.val u.property).2.2.2)] with p hm hn ha hu hda hdu
    have hz : p ∈ actualZeroRelation W m S.ρ :=
      ⟨hm, fun he => hau (Subtype.ext (ha.symm.trans (he.trans hu)))⟩
    simpa only [hda, hdu] using hn hz
  obtain ⟨x, _, hx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers a.val a.property).2.1.ne' (Measure.ae_ae_of_ae_prod hgood)
  obtain ⟨y, _, hy⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers u.val u.property).2.1.ne' hx
  exact hy

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

private theorem no_positive_exchange_region
    (S : SelectedHighLowStructure W m) (r a u : S.I) (hru : r ≠ u) (hau : a ≠ u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (E : Set Ω) (hE : MeasurableSet E) (hED : E ⊆ S.D)
    (hEA : E ⊆ S.rootNeighborhood a) (hEU : E ⊆ (S.rootNeighborhood u)ᶜ)
    (hEpos : 0 < μ E) : False := by
  let R := {x | S.ρ x = r.val}
  let P := {x | S.ρ x = a.val}
  let Q := {x | S.ρ x = u.val}
  let G := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  let s (x : Ω) := max 0 (S.rootChargeRow r x)
  have hP : MeasurableSet P := (S.hfibers a.val a.property).1
  have hQ : MeasurableSet Q := (S.hfibers u.val u.property).1
  have hPpos : 0 < μ P := (S.hfibers a.val a.property).2.1
  have hQpos : 0 < μ Q := (S.hfibers u.val u.property).2.1
  have hPQ : Disjoint P Q := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hau (Subtype.ext (hx.symm.trans hy))
  have hRE : Disjoint R E := Set.disjoint_left.mpr (fun x hx hy =>
    S.row_ne_atom_of_mem_diffuse x (hED hy) r hx)
  have hPE : Disjoint P E := Set.disjoint_left.mpr (fun x hx hy =>
    S.row_ne_atom_of_mem_diffuse x (hED hy) a hx)
  have hQE : Disjoint Q E := Set.disjoint_left.mpr (fun x hx hy =>
    S.row_ne_atom_of_mem_diffuse x (hED hy) u hx)
  have hRQ : Disjoint R Q := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hru (Subtype.ext (hx.symm.trans hy))
  have hs : Measurable s := measurable_const.max (S.measurable_rootChargeRow r)
  have hsbox (x : Ω) : s x ∈ Icc (0 : ℝ) 1 :=
    ⟨le_max_left _ _, max_le (by norm_num) (S.rootChargeRow_mem_Icc r x).2⟩
  have hseq : ∀ᵐ x ∂μ, x ∈ E → s x = S.rootChargeRow r x := by
    filter_upwards [S.ae_rootChargeRow_pos_of_zero_body r hW hd hgap hzero] with x hx hxE
    exact max_eq_right (hx (S.row_ne_atom_of_mem_diffuse x (hED hxE) r)).le
  let ε := min (μ.real P) (μ.real Q) / 2
  have hpReal : 0 < μ.real P := ENNReal.toReal_pos hPpos.ne' (measure_ne_top _ _)
  have hqReal : 0 < μ.real Q := ENNReal.toReal_pos hQpos.ne' (measure_ne_top _ _)
  have hε : 0 < ε := div_pos (lt_min hpReal hqReal) (by norm_num)
  have hεP : ε < μ.real P := by dsimp only [ε]; linarith [min_le_left (μ.real P) (μ.real Q)]
  have hεQ : ε < μ.real Q := by dsimp only [ε]; linarith [min_le_right (μ.real P) (μ.real Q)]
  obtain ⟨K, P', hKP, hP'P, hK, hP', hKP', hKmass, hKpos, hP'pos⟩ :=
    exists_piece_and_positive_remainder P hP hPpos ε hε hεP
  obtain ⟨J, Q', hJQ, hQ'Q, hJ, hQ', hJQ', hJmass, _, hQ'pos⟩ :=
    exists_piece_and_positive_remainder Q hQ hQpos ε hε hεQ
  have hRJ : Disjoint R J := hRQ.mono_right hJQ
  have hJE : Disjoint J E := hQE.mono_left hJQ
  have hKE : Disjoint K E := hPE.mono_left hKP
  have hgapData := hW.strict_gap_structure hd hgap
  have hWmom : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      (if G p.1 p.2 = true then 1 else 0) ∧ W.moment CappedColor.charge p = Y p.1 p.2 := by
    filter_upwards [PhysicalRepresentative.adjacency_moment_ae_eq W m hgapData.strict_support,
      PhysicalRepresentative.charge_ae_eq W m hgapData.strict_support] with p hg hy
    exact ⟨hg, hy.symm⟩
  have hroot : ∀ᵐ p ∂μ.prod μ, p.1 ∈ R → p.2 ∈ R → G p.1 p.2 = false := by
    filter_upwards [S.neutral_atom_physical_adjacency r hW hd hgap hN] with p hp hx hy
    apply Bool.eq_false_iff.mpr
    intro he
    exact (hp hx).mp he hy
  have hbody : ∀ᵐ p ∂μ.prod μ, p.1 ∉ R → p.2 ∉ R → Y p.1 p.2 ≤ 0 := by
    filter_upwards [S.zero_body_ae_charge_nonpositive r hzero,
      PhysicalRepresentative.charge_ae_eq W m hgapData.strict_support] with p hp he hx hy
    change PhysicalRepresentative.charge W m p.1 p.2 ≤ 0
    rw [he]
    exact hp hx hy
  have hstar : ∀ᵐ p ∂μ.prod μ, p.1 ∈ R → p.2 ∈ E → Y p.1 p.2 = s p.2 := by
    filter_upwards [S.ae_root_charge r hW hd hgap,
      Measure.quasiMeasurePreserving_snd.ae hseq] with p hp he hx hy
    exact (hp hx).trans (he hy).symm
  have hQr : ∀ᵐ p ∂μ.prod μ, p.1 ∈ Q → p.2 ∈ E → G p.1 p.2 = false := by
    filter_upwards [S.ae_root_adjacency u hW hd hgap] with p hp hx hy
    apply Bool.eq_false_iff.mpr
    intro he
    exact hEU hy ((hp hx).mp he)
  have hPr : ∀ᵐ p ∂μ.prod μ, p.1 ∈ P → p.2 ∈ E →
      G p.1 p.2 = true ∧ Y p.1 p.2 = -s p.2 ∧ s p.2 + m < 0 := by
    filter_upwards [S.ae_root_adjacency a hW hd hgap,
      S.ae_saturated_head_charge_cancel_of_zero_body r a hW hd hgap hN hpair hzero,
      hWmom, hgapData.strict_support, Measure.quasiMeasurePreserving_snd.ae hseq]
      with p hp hc hm hsupport he hx hy
    have hG : G p.1 p.2 = true := (hp hx).mpr (hEA hy)
    have hGold : adjacencyKernel W p.1 p.2 = 1 := by
      change W.moment CappedColor.adjacency p = 1
      simpa only [hG, ite_true] using hm.1
    have hcan := hc hx (S.row_ne_atom_of_mem_diffuse p.2 (hED hy) r) hGold
    have hYold : chargeKernel W p.1 p.2 = Y p.1 p.2 := hm.2
    have hY : Y p.1 p.2 = -s p.2 := by
      rw [hYold, ← he hy] at hcan
      linarith
    refine ⟨hG, hY, ?_⟩
    have hpos : 0 < shiftedMoment W m p := by
      by_contra hn
      rw [ite_eq_right hn] at hsupport
      change W.moment CappedColor.adjacency p = 1 at hGold
      linarith
    rw [shiftedMoment_eq] at hpos
    change W.moment CappedColor.adjacency p = 1 at hGold
    rw [hGold, hm.2, hY] at hpos
    linarith
  have hsStrict : ∀ᵐ x ∂μ.restrict E, s x + m < 0 := by
    obtain ⟨x, hx, hr⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hPpos.ne'
      (ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hPr))
    filter_upwards [ae_restrict_of_ae hr, ae_restrict_mem hE] with y hy hyE
    exact (hy hx hyE).2.2
  have hJrect : ∀ᵐ p ∂μ.prod μ, FiniteArity.extensionPair J E p.1 p.2 → G p.1 p.2 = false := by
    have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hQr
    filter_upwards [hQr, hswap] with p hp hq hrect
    rcases hrect with h | h
    · exact hp (hJQ h.1) h.2
    · dsimp only [G]
      rw [PhysicalRepresentative.adjacency_symm]
      exact hq (hJQ h.1) h.2
  have hKrect : ∀ᵐ p ∂μ.prod μ, FiniteArity.extensionPair K E p.1 p.2 →
      G p.1 p.2 = true ∧ Y p.1 p.2 = -(E.indicator s p.1 + E.indicator s p.2) := by
    have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hPr
    filter_upwards [hPr, hswap] with p hp hq hrect
    rcases hrect with h | h
    · have hxE : p.1 ∉ E := fun hx => Set.disjoint_left.mp hKE h.1 hx
      obtain ⟨hg, hy, _⟩ := hp (hKP h.1) h.2
      exact ⟨hg, by simpa only [indicator_of_notMem hxE, indicator_of_mem h.2, zero_add] using hy⟩
    · have hyE : p.2 ∉ E := fun hy => Set.disjoint_left.mp hKE h.1 hy
      obtain ⟨hg, hy, _⟩ := hq (hKP h.1) h.2
      constructor
      · dsimp only [G]
        rw [PhysicalRepresentative.adjacency_symm]
        exact hg
      · dsimp only [Y]
        rw [PhysicalRepresentative.charge_symm]
        simpa only [Y, Prod.swap, indicator_of_mem h.2, indicator_of_notMem hyE, add_zero] using hy
  obtain ⟨V, hV, hdV, hcV, hVrows⟩ := NeighborhoodExchange.exists_neutral_model W
    G (PhysicalRepresentative.measurable_adjacency W m) (PhysicalRepresentative.adjacency_symm W m)
    Y (PhysicalRepresentative.measurable_charge W m) (PhysicalRepresentative.charge_symm W m)
    (PhysicalRepresentative.charge_mem_Icc W m) (PhysicalRepresentative.charge_zero_of_nonedge W m)
    hWmom s hs hsbox R J E K hJ hE hK hRJ hRE hJE hKE (hJmass.trans hKmass.symm)
    hroot hbody hstar hJrect hKrect
    (PhysicalRepresentative.full_feasible W hW.full m hgapData.strict_support hW.deterministic)
  have hgNe := S.degree_ne_of_missing_fibers a u hau hW hd hgap
    (S.ae_saturated_head_atom_adjacency_zero_of_zero_body r a u hru hW hd hgap hN hpair hzero)
  have hopt : objective V = FractionalGraph.densityLimit (density V) := by
    rw [hcV, hdV, hW.objective_eq, hW.density_eq]
    exact hW.optimal
  have hPU : ∀ᵐ x ∂μ.restrict P',
      (∫ y, adjacencyKernel V x y ∂μ) = wholeRowDegree a.val ∧
      (∫ y, chargeKernel V x y ∂μ) = 2 * (c - m * d) + m * wholeRowDegree a.val := by
    filter_upwards [ae_restrict_of_ae hVrows,
      ae_mono (Measure.restrict_mono hP'P le_rfl) (S.ae_fiber_moment_rows a hW),
      ae_restrict_mem hP'] with x hv ho hx
    have hxK : x ∉ K := fun hk => Set.disjoint_left.mp hKP' hk hx
    have hxJ : x ∉ J := fun hj => Set.disjoint_left.mp hPQ (hP'P hx) (hJQ hj)
    simpa only [indicator_of_notMem hxK, indicator_of_notMem hxJ, sub_self, zero_mul,
      add_zero, sub_zero, ho.1, ho.2] using hv
  have hQU : ∀ᵐ x ∂μ.restrict Q',
      (∫ y, adjacencyKernel V x y ∂μ) = wholeRowDegree u.val ∧
      (∫ y, chargeKernel V x y ∂μ) = 2 * (c - m * d) + m * wholeRowDegree u.val := by
    filter_upwards [ae_restrict_of_ae hVrows,
      ae_mono (Measure.restrict_mono hQ'Q le_rfl) (S.ae_fiber_moment_rows u hW),
      ae_restrict_mem hQ'] with x hv ho hx
    have hxJ : x ∉ J := fun hj => Set.disjoint_left.mp hJQ' hj hx
    have hxK : x ∉ K := fun hk => Set.disjoint_left.mp hPQ (hKP hk) (hQ'Q hx)
    simpa only [indicator_of_notMem hxK, indicator_of_notMem hxJ, sub_self, zero_mul,
      add_zero, sub_zero, ho.1, ho.2] using hv
  have hVstat := full_stationary_of_two_retained_degree_values V hV hopt P' Q' hP'pos hQ'pos
    (wholeRowDegree a.val) (wholeRowDegree u.val) m (2 * (c - m * d)) hgNe hPU hQU
  have hVG : Integrable (fun p : Ω × Ω => adjacencyKernel V p.1 p.2) (μ.prod μ) :=
    Integrable.of_bound (adjacencyKernel_measurable V) 1 (adjacencyKernel_bound V)
  have hVY : Integrable (fun p : Ω × Ω => chargeKernel V p.1 p.2) (μ.prod μ) :=
    Integrable.of_bound (chargeKernel_measurable V) 3 (chargeKernel_bound V)
  have hKold : ∀ᵐ x ∂μ.restrict K,
      (∫ y, adjacencyKernel W x y ∂μ) = wholeRowDegree a.val ∧
      (∫ y, chargeKernel W x y ∂μ) = 2 * (c - m * d) + m * wholeRowDegree a.val :=
    ae_mono (Measure.restrict_mono hKP le_rfl) (S.ae_fiber_moment_rows a hW)
  obtain ⟨x, hxK, hxStat, hxRows, hxOld, hxG, hxY⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hKpos.ne'
    ((ae_restrict_of_ae hVstat).and ((ae_restrict_of_ae hVrows).and
      (hKold.and ((ae_restrict_of_ae hVG.prod_right_ae).and (ae_restrict_of_ae hVY.prod_right_ae)))))
  have hxJ : x ∉ J := fun hj => Set.disjoint_left.mp hPQ (hKP hxK) (hJQ hj)
  simp only [indicator_of_notMem hxJ, indicator_of_mem hxK] at hxRows
  have hMeq : (fun y => shiftedKernel V m x y) =
      fun y => chargeKernel V x y - m * adjacencyKernel V x y := by
    funext y
    exact shiftedMoment_eq V m (x, y)
  rw [hMeq, integral_sub hxY (hxG.const_mul m), integral_const_mul, hxRows.1, hxRows.2,
    hxOld.1, hxOld.2] at hxStat
  have heq : (∫ y in E, s y ∂μ) + m * μ.real E = 0 := by nlinarith
  have hsint : Integrable s μ := Integrable.of_bound hs.aestronglyMeasurable 1
    (Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hsbox x).1]
      exact (hsbox x).2))
  have hfint : Integrable (fun x => -(s x + m)) (μ.restrict E) :=
    (hsint.integrableOn.add (integrable_const m)).neg
  have hfnonneg : ∀ᵐ x ∂μ.restrict E, 0 ≤ -(s x + m) := hsStrict.mono (fun _ h => by linarith)
  have hfzero : (∫ x in E, -(s x + m) ∂μ) = 0 := by
    rw [integral_neg, integral_add hsint.integrableOn (integrable_const m),
      setIntegral_const, smul_eq_mul]
    nlinarith [heq]
  have hfae := (integral_eq_zero_iff_of_nonneg_ae hfnonneg hfint).mp hfzero
  obtain ⟨y, _, hy, hy0⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hEpos.ne' (hsStrict.and hfae)
  change -(s y + m) = 0 at hy0
  linarith

/-- In the same zero-body strict-gap model, an exterior atom cannot miss
positive diffuse mass joined to the saturated head. The actual neutral
exchange and the edited optimum's own multiplier are constructed inside
the proof, with positive old remainders retained on both atoms. -/
theorem measure_diffuse_saturated_neighbor_gap_eq_zero
    (S : SelectedHighLowStructure W m) (r a u : S.I) (hru : r ≠ u) (hau : a ≠ u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) :
    μ {x | x ∈ S.D ∧ x ∈ S.rootNeighborhood a ∧ x ∉ S.rootNeighborhood u} = 0 := by
  by_contra hn
  let E := {x | x ∈ S.D ∧ x ∈ S.rootNeighborhood a ∧ x ∉ S.rootNeighborhood u}
  have hE : MeasurableSet E := S.hD.inter
    ((S.measurableSet_rootNeighborhood a).inter (S.measurableSet_rootNeighborhood u).compl)
  exact S.no_positive_exchange_region r a u hru hau hW hd hgap hN hpair hzero E hE
    (fun _ h => h.1) (fun _ h => h.2.1) (fun _ h => h.2.2) (pos_iff_ne_zero.mpr hn)

/-- The source's neighborhood-exchange conclusion is an actual original
adjacency statement on every exterior independent whole atom and the
diffuse neighborhood of its saturated head. -/
theorem ae_atom_sees_diffuse_saturated_neighbors_of_zero_body
    (S : SelectedHighLowStructure W m) (r a u : S.I) (hru : r ≠ u) (hau : a ≠ u)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hN : ∀ᵐ x ∂μ.restrict {x | S.ρ x = r.val}, x ∈ S.N)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) :
    ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = u.val → p.2 ∈ S.D → p.2 ∈ S.rootNeighborhood a →
      adjacencyKernel W p.1 p.2 = 1 := by
  have hnull := S.measure_diffuse_saturated_neighbor_gap_eq_zero r a u hru hau hW hd hgap hN hpair hzero
  have hgood : ∀ᵐ x ∂μ, x ∈ S.D → x ∈ S.rootNeighborhood a → x ∈ S.rootNeighborhood u := by
    filter_upwards [(measure_eq_zero_iff_ae_notMem).mp hnull] with x hx hD hA
    by_contra hU
    exact hx ⟨hD, hA, hU⟩
  filter_upwards [S.ae_root_adjacency u hW hd hgap,
    Measure.quasiMeasurePreserving_snd.ae hgood,
    PhysicalRepresentative.adjacency_moment_ae_eq W m (hW.strict_gap_structure hd hgap).strict_support]
    with p hu hg hm hpU hpD hpA
  have he := (hu hpU).mpr (hg hpD hpA)
  change W.moment CappedColor.adjacency p = 1
  simpa only [he, ite_true] using hm

end Erdos1017.CappedModel.SelectedHighLowStructure
