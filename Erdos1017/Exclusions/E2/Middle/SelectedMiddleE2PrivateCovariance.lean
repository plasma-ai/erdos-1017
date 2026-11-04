module

public import Erdos1017.Exclusions.E2.Upper.SelectedUpperE2PrivateCovarianceGeometry

/-!
# Curvature covariance in the private sector

The Schur complement of the three bounded directions (`curvature_schur`), the
exact whole-atom degrees of the private geometry
(`private_wholeRowDegrees_sector`), and the curvature covariance of the
mean-zero directions `ρ_P - 1`, `A(ρ_P - ρ_I)`, `k(ρ_P - ρ_K)`
(`private_curvature_covariance`) are proved here.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Classical RealInnerProductSpace

namespace Erdos1017.MiddleE2PrivateScalar

/-- The Schur complement of the three bounded directions. If every
combination `wK + y wI + w f` obeys the curvature test, the exposure
`E > k` forces `D^2 < ν (2k(A+k) - 1/C)`. -/
theorem curvature_schur {A k D ν C DK E Q : ℝ}
    (hA : 0 < A) (hk : 0 < k) (hν : 0 < ν) (hC : 0 < C)
    (hDK : DK ≤ k * (A + k)) (hE : k < E) (hQ : 0 ≤ Q)
    (hall : ∀ y w : ℝ, Q + 2 * y * A * E - w ^ 2 * ν ≤
      C * (DK + y * A * k + w * D) ^ 2) :
    D ^ 2 < ν * (2 * k * (A + k) - 1 / C) := by
  by_contra hneg
  have hneg' : ν * (2 * k * (A + k) - 1 / C) ≤ D ^ 2 := le_of_not_gt hneg
  have hΔ : 0 < ν + C * D ^ 2 := by positivity
  have hEpos : 0 < E := hk.trans hE
  have hCν : 0 < C * ν * k := by positivity
  have hcap : 2 * C * ν * k * (A + k) ≤ ν + C * D ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hneg' hC.le
    have heq : C * (ν * (2 * k * (A + k) - 1 / C)) = 2 * C * ν * k * (A + k) - ν := by
      field_simp
    linarith
  obtain ⟨l, hl⟩ : ∃ l, l = E * (ν + C * D ^ 2) / (C * ν * k) := ⟨_, rfl⟩
  have hkey := hall ((l - DK) / (A * k)) (-(C * l * D / (ν + C * D ^ 2)))
  have h1 : DK + (l - DK) / (A * k) * A * k + -(C * l * D / (ν + C * D ^ 2)) * D =
      l * ν / (ν + C * D ^ 2) := by
    field_simp
    ring
  have h2 : 2 * ((l - DK) / (A * k)) * A * E = 2 * E * (l - DK) / k := by
    field_simp
  have h3 : C * (l * ν / (ν + C * D ^ 2)) ^ 2 +
      (-(C * l * D / (ν + C * D ^ 2))) ^ 2 * ν = l * E / k := by
    rw [hl]
    field_simp
  rw [h1, h2] at hkey
  have hstep : 2 * E * (l - DK) / k ≤ l * E / k := by linarith
  have hl2 : l ≤ 2 * DK := by
    have h := mul_le_mul_of_nonneg_right hstep hk.le
    field_simp at h
    linarith
  have hEΔ : E * (ν + C * D ^ 2) ≤ 2 * DK * (C * ν * k) := by
    have h := mul_le_mul_of_nonneg_right hl2 hCν.le
    rw [hl, div_mul_cancel₀ _ hCν.ne'] at h
    exact h
  have hDKC : 2 * DK * (C * ν * k) ≤ k * (2 * C * ν * k * (A + k)) := by
    have h := mul_le_mul_of_nonneg_right hDK (show 0 ≤ 2 * (C * ν * k) by positivity)
    nlinarith
  have hfinal : E * (ν + C * D ^ 2) ≤ k * (ν + C * D ^ 2) :=
    hEΔ.trans (hDKC.trans (mul_le_mul_of_nonneg_left hcap hk.le))
  have := le_of_mul_le_mul_right hfinal hΔ
  linarith

end Erdos1017.MiddleE2PrivateScalar

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem wholeRowDegree_eq_rootNeighborhood
    (S : SelectedHighLowStructure W m) (r : S.I) :
    wholeRowDegree r.val = μ.real (S.rootNeighborhood r) := by
  have hN := S.measurableSet_rootNeighborhood r
  have heq : (fun x => if 0 < (r.val : Ω → ℝ) x then (1 : ℝ) else 0) =ᵐ[μ]
      (S.rootNeighborhood r).indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [S.ae_rootNeighborhood_iff r] with x hx
    by_cases hr : 0 < (r.val : Ω → ℝ) x
    · simp [hr, (hx.mpr hr)]
    · simp [hr, (not_iff_not.mpr hx).mpr hr]
  rw [wholeRowDegree, integral_congr_ae heq]
  exact integral_indicator_one hN

private theorem ae_private_second_root_off_first
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

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
private theorem ae_whole_row_zero_off_root
    (S : SelectedHighLowStructure W m) (r : S.I)
    (T : Set Ω)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hoff : ∀ᵐ x ∂μ.restrict T, x ∉ S.rootNeighborhood r) :
    ∀ᵐ x ∂μ.restrict T, (r.val : Ω → ℝ) x = 0 := by
  filter_upwards [hoff, ae_restrict_of_ae (S.ae_rootNeighborhood_iff r),
    ae_restrict_of_ae (S.ae_whole_row_nonneg r hW)] with x hx hiff hnonneg
  exact le_antisymm (le_of_not_gt (fun h => hx (hiff.mpr h))) hnonneg

/-- The literal private geometry gives the exact degrees of both whole
atoms: `1 - A - b` and `n = 1 - A - b - k`. -/
theorem private_wholeRowDegrees_sector
    (S : SelectedHighLowStructure W m) (i p : S.I) (hip : i ≠ p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hprivate : ∀ᵐ q ∂μ.prod μ, S.ρ q.1 = i.val →
      adjacencyKernel W q.1 q.2 =
        if S.ρ q.2 = i.val ∨ S.ρ q.2 = p.val then 0 else 1) :
    wholeRowDegree i.val = 1 - μ.real {x | S.ρ x = i.val} - μ.real {x | S.ρ x = p.val} ∧
      μ.real (S.rootNeighborhood p) = 1 - μ.real {x | S.ρ x = i.val} -
        μ.real {x | S.ρ x = p.val} -
        μ.real (({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ \ S.rootNeighborhood p) := by
  let I := {x | S.ρ x = i.val}
  let P := {x | S.ρ x = p.val}
  let E := I ∪ P
  let N := S.rootNeighborhood p
  let K := Eᶜ \ N
  have hI : MeasurableSet I := (S.hfibers i.val i.property).1
  have hP : MeasurableSet P := (S.hfibers p.val p.property).1
  have hE : MeasurableSet E := hI.union hP
  have hK : MeasurableSet K := hE.compl.diff (S.measurableSet_rootNeighborhood p)
  have hdis : Disjoint I P := disjoint_left.mpr (fun _ hi hp =>
    hip (Subtype.ext (hi.symm.trans hp)))
  have hNi : S.rootNeighborhood i =ᵐ[μ] Eᶜ :=
    (S.ae_private_rootNeighborhood_iff i p hW hd hgap hprivate).mono
      (fun _ hx => propext (by simpa only [E, I, P, mem_compl_iff, mem_union,
        mem_ofPred_eq, not_or] using hx))
  have hNpI := S.ae_private_second_root_off_first i p hW hd hgap hprivate
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
  constructor
  · rw [S.wholeRowDegree_eq_rootNeighborhood i, measureReal_congr hNi]
    exact hEreal
  · exact hNreal

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem adjacency_inner_normalizedHead
    (S : SelectedHighLowStructure W m) (r : S.I) :
    ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), S.normalizedHead r⟫ =
      wholeRowDegree r.val := by
  rw [real_inner_comm]
  exact KernelOperator.normalizedSetL2_inner_of_constant _ _
    (S.hfibers r.val r.property).2.1 _ _
    (wholeRowFiber_degree W m S.ρ r.val (S.hfibers r.val r.property).2.2.2)

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem adjacency_inner_one {d c : ℝ}
    (hW : FullStationaryClass d c W m) :
    ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), Lp.const 2 μ (1 : ℝ)⟫ =
      2 * d := by
  rw [← weighted_adjacency_eq, weightedPairIntegral_one]
  have hdW := hW.density_eq
  unfold density at hdW
  change (∫ q, adjacencyKernel W q.1 q.2 ∂μ.prod μ) / 2 = d at hdW
  linarith

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem normalizedSetL2_inner_le_of_ae_le (s : Set Ω)
    (hs : MeasurableSet s) (hspos : 0 < μ s) (f : Lp ℝ 2 μ) (a : ℝ)
    (hf : ∀ᵐ x ∂μ.restrict s, f x ≤ a) :
    ⟪f, KernelOperator.normalizedSetL2 s hs⟫ ≤ a := by
  have hi : Integrable (fun x => f x) (μ.restrict s) :=
    ((Lp.memLp f).integrable (by norm_num)).integrableOn
  have hint := integral_mono_ae hi (integrable_const a) hf
  have hmasspos : 0 < μ.real s := ENNReal.toReal_pos hspos.ne' (measure_ne_top μ _)
  rw [setIntegral_const, smul_eq_mul] at hint
  rw [real_inner_comm, KernelOperator.normalizedSetL2_inner]
  calc
    _ ≤ (μ.real s)⁻¹ * (μ.real s * a) :=
      mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hmasspos.le)
    _ = a := by field_simp

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
private theorem ae_zero_rect_of_row_zero
    (S : SelectedHighLowStructure W m) (p : S.I)
    (T : Set Ω)
    (hzero : ∀ᵐ x ∂μ.restrict T, (p.val : Ω → ℝ) x = 0) :
    ∀ᵐ q ∂(μ.restrict {x | S.ρ x = p.val}).prod (μ.restrict T),
      shiftedKernel W m q.1 q.2 = 0 := by
  have hle : (μ.restrict {x | S.ρ x = p.val}).prod (μ.restrict T) ≤ μ.prod μ :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  filter_upwards [ae_mono hle (S.ae_kernel_eq_fiber_row p.val p.property),
    Measure.quasiMeasurePreserving_fst.ae
      (ae_restrict_mem (S.hfibers p.val p.property).1),
    Measure.quasiMeasurePreserving_snd.ae hzero] with q hrow hp hz
  exact (hrow hp).trans hz

private theorem private_hole_degree_le_one_sub_second_mass
    (S : SelectedHighLowStructure W m) (i p : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hk : 0 < μ (({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ \
      S.rootNeighborhood p)) :
    ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)),
      KernelOperator.normalizedSetL2 (({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ \
        S.rootNeighborhood p) ((S.hfibers i.val i.property).1.union
        (S.hfibers p.val p.property).1 |>.compl.diff
          (S.measurableSet_rootNeighborhood p))⟫ ≤
        1 - μ.real {x | S.ρ x = p.val} := by
  let P := {x | S.ρ x = p.val}
  let K := ({x | S.ρ x = i.val} ∪ P)ᶜ \ S.rootNeighborhood p
  let g := adjacencyOperator W (Lp.const 2 μ (1 : ℝ))
  have hP := (S.hfibers p.val p.property).1
  have hK : MeasurableSet K :=
    ((S.hfibers i.val i.property).1.union hP).compl.diff
      (S.measurableSet_rootNeighborhood p)
  have hOff : ∀ᵐ x ∂μ.restrict K, x ∉ S.rootNeighborhood p :=
    (ae_restrict_mem hK).mono (fun _ hx => hx.2)
  have hpzero := S.ae_whole_row_zero_off_root p K hW hOff
  have hzero := S.ae_zero_rect_of_row_zero p K hpzero
  have hAdjPK : ∀ᵐ q ∂(μ.restrict P).prod (μ.restrict K),
      adjacencyKernel W q.1 q.2 = 0 := by
    have hle : (μ.restrict P).prod (μ.restrict K) ≤ μ.prod μ :=
      Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
    filter_upwards [hzero,
      ae_mono hle (hW.strict_gap_structure hd hgap).strict_support] with q hz hs
    change adjacencyKernel W q.1 q.2 =
      (if 0 < shiftedKernel W m q.1 q.2 then 1 else 0) at hs
    rw [hz] at hs
    simpa only [lt_irrefl, ↓reduceIte] using hs
  have hswap := (Measure.measurePreserving_swap
    (μ := μ.restrict K) (ν := μ.restrict P)).quasiMeasurePreserving
  have hAdjKP : ∀ᵐ q ∂(μ.restrict K).prod (μ.restrict P),
      adjacencyKernel W q.1 q.2 = 0 := by
    have hle : (μ.restrict K).prod (μ.restrict P) ≤ μ.prod μ :=
      Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
    filter_upwards [hswap.ae hAdjPK, ae_mono hle (adjacencyKernel_symm W)]
      with q hz hs
    change adjacencyKernel W q.2 q.1 = 0 at hz
    exact hs.trans hz
  have hsec := Measure.ae_ae_of_ae_prod hAdjKP
  have hbound : ∀ᵐ x ∂μ.restrict K, g x ≤ 1 - μ.real P := by
    filter_upwards [hsec,
      ae_restrict_of_ae (KernelOperator.onL2_coe (adjacencyKernel W)
        (adjacencyKernel_measurable W) (adjacencyKernel_bound W)
        (Lp.const 2 μ (1 : ℝ)))] with x hx hg
    have hzeroP := (ae_restrict_iff' hP).mp hx
    have hpoint : ∀ᵐ y ∂μ,
        adjacencyKernel W x y ≤ 1 - P.indicator (fun _ => (1 : ℝ)) y := by
      filter_upwards [hzeroP] with y hy
      by_cases hp : y ∈ P
      · rw [hy hp, indicator_of_mem hp]
        norm_num
      · simp only [indicator_of_notMem hp, sub_zero]
        exact (adjacency_moment_mem W (x, y)).2
    have hi : Integrable (adjacencyKernel W x) μ := Integrable.of_bound
      ((W.stronglyMeasurable_moment
        CappedColor.continuous_adjacency.measurable.stronglyMeasurable).comp_measurable
          (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
      (Eventually.of_forall (fun y => by
        change ‖W.moment CappedColor.adjacency (x, y)‖ ≤ 1
        rw [Real.norm_eq_abs, abs_of_nonneg (adjacency_moment_mem W (x, y)).1]
        exact (adjacency_moment_mem W (x, y)).2))
    have hiP : Integrable (P.indicator (fun _ => (1 : ℝ))) μ :=
      (integrable_const 1).indicator hP
    have hle' := integral_mono_ae hi ((integrable_const 1).sub hiP) hpoint
    change (∫ y, adjacencyKernel W x y ∂μ) ≤
      ∫ y, (1 : ℝ) - P.indicator (fun _ => (1 : ℝ)) y ∂μ at hle'
    rw [integral_sub (integrable_const 1) hiP, integral_const, probReal_univ,
      one_smul] at hle'
    have hiPeq : (∫ y, P.indicator (fun _ => (1 : ℝ)) y ∂μ) = μ.real P :=
      integral_indicator_one hP
    rw [hiPeq] at hle'
    have hgeq : g x = ∫ y, adjacencyKernel W x y ∂μ := by
      change g x = KernelOperator.applyKernel (adjacencyKernel W)
        (Lp.const 2 μ (1 : ℝ)) x at hg
      rw [hg, KernelOperator.applyKernel]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_const 2 μ (1 : ℝ)] with y hy
      simp only [hy, Function.const_apply, mul_one]
    rw [hgeq]
    exact hle'
  exact normalizedSetL2_inner_le_of_ae_le K hK hk g _ hbound

/-- The three bounded mean-zero directions `ρ_P - 1`, `A(ρ_P - ρ_I)` and
`k(ρ_P - ρ_K)` of the same original model, tested against an explicit
curvature coefficient `C`, give the Schur bound
`(A + b + k - h)^2 < ν (2k(A+k) - 1/C)`. -/
theorem private_curvature_covariance
    (S : SelectedHighLowStructure W m) (i p : S.I) (hip : i ≠ p)
    {d c C : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hprivate : ∀ᵐ q ∂μ.prod μ, S.ρ q.1 = i.val →
      adjacencyKernel W q.1 q.2 =
        if S.ρ q.2 = i.val ∨ S.ρ q.2 = p.val then 0 else 1)
    (hC : 0 < C)
    (hcurv : ∀ f : Lp ℝ 2 μ, f ∈ KernelOperator.boundedL2Submodule μ →
      (∫ x, f x ∂μ) = 0 →
      ⟪shiftedOperator W m f, f⟫ ≤ C * ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)), f⟫ ^ 2)
    (hk : 0 < μ (({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ \
      S.rootNeighborhood p))
    (hE : μ.real (({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ \
      S.rootNeighborhood p) <
      ∫ z in (({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ \
        S.rootNeighborhood p), (i.val : Ω → ℝ) z ∂μ) :
    (μ.real {x | S.ρ x = i.val} + μ.real {x | S.ρ x = p.val} +
        μ.real (({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ \ S.rootNeighborhood p) -
        (1 - 2 * d)) ^ 2 <
      2 * (c - m * d) *
        (2 * μ.real (({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ \ S.rootNeighborhood p) *
          (μ.real {x | S.ρ x = i.val} +
            μ.real (({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ \ S.rootNeighborhood p)) -
          1 / C) := by
  let I := {x | S.ρ x = i.val}
  let P := {x | S.ρ x = p.val}
  let K := (I ∪ P)ᶜ \ S.rootNeighborhood p
  have hI : MeasurableSet I := (S.hfibers i.val i.property).1
  have hK : MeasurableSet K :=
    ((S.hfibers i.val i.property).1.union (S.hfibers p.val p.property).1).compl.diff
      (S.measurableSet_rootNeighborhood p)
  let A := μ.real I
  let b := μ.real P
  let k := μ.real K
  let a := S.normalizedHead i
  let bh := S.normalizedHead p
  let z := KernelOperator.normalizedSetL2 (μ := μ) K hK
  let e := Lp.const 2 μ (1 : ℝ)
  let g := adjacencyOperator W e
  let B := schurForm W m
  let ν := 2 * (c - m * d)
  let E := ∫ x in K, (i.val : Ω → ℝ) x ∂μ
  let f := bh - e
  let wI := A • (bh - a)
  let wK := k • (bh - z)
  have hA : 0 < A := ENNReal.toReal_pos (S.hfibers i.val i.property).2.1.ne'
    (measure_ne_top μ I)
  have hk' : 0 < k := ENNReal.toReal_pos hk.ne' (measure_ne_top μ K)
  have hν : 0 < ν := (hW.strict_gap_structure hd hgap).stationary_pos
  have hdegrees := S.private_wholeRowDegrees_sector i p hip hW hd hgap hprivate
  have hdegI : wholeRowDegree i.val = 1 - A - b := hdegrees.1
  have hdegP : wholeRowDegree p.val = 1 - A - b - k := by
    rw [S.wholeRowDegree_eq_rootNeighborhood p]
    exact hdegrees.2
  have hgi : ⟪g, a⟫ = wholeRowDegree i.val := S.adjacency_inner_normalizedHead i
  have hgp : ⟪g, bh⟫ = wholeRowDegree p.val := S.adjacency_inner_normalizedHead p
  have hge : ⟪g, e⟫ = 2 * d := adjacency_inner_one hW
  have hupper : ⟪g, z⟫ ≤ 1 - b :=
    S.private_hole_degree_le_one_sub_second_mass i p hW hd hgap hk
  have hPI : ∀ᵐ x ∂μ.restrict I, (p.val : Ω → ℝ) x = 0 :=
    S.ae_whole_row_zero_off_root p I hW
      (S.ae_private_second_root_off_first i p hW hd hgap hprivate)
  have hPK : ∀ᵐ x ∂μ.restrict K, (p.val : Ω → ℝ) x = 0 :=
    S.ae_whole_row_zero_off_root p K hW
      ((ae_restrict_mem hK).mono (fun _ hx => hx.2))
  let D := A + b + k - (1 - 2 * d)
  let DK := k * (⟪g, z⟫ - ⟪g, bh⟫)
  have hDKupper : DK ≤ k * (A + k) := by
    have hdiff : ⟪g, z⟫ - ⟪g, bh⟫ ≤ A + k := by
      rw [hgp, hdegP]
      linarith [hupper]
    exact mul_le_mul_of_nonneg_left hdiff hk'.le
  have haa : B a a = 0 := S.schurForm_head_self i
  have hbb : B bh bh = 0 := S.schurForm_head_self p
  have hsym (x y : Lp ℝ 2 μ) : B x y = B y x := schurForm_symm x y
  have hbe : B e bh = ν := S.schurForm_constant_head p hW
  have hee : B e e = ν := schurForm_constant_self hW
  have hba : B bh a = 0 := by
    change ⟪shiftedOperator W m bh, a⟫ = 0
    rw [S.operator_normalizedHead p, real_inner_comm]
    exact KernelOperator.normalizedSetL2_inner_of_constant I hI
      (S.hfibers i.val i.property).2.1 p.val 0 hPI
  have hbz : B bh z = 0 := by
    change ⟪shiftedOperator W m bh, z⟫ = 0
    rw [S.operator_normalizedHead p, real_inner_comm]
    exact KernelOperator.normalizedSetL2_inner_of_constant K hK hk p.val 0 hPK
  have haz : B a z = k⁻¹ * E := by
    change ⟪shiftedOperator W m a, z⟫ = _
    rw [S.operator_normalizedHead i, real_inner_comm]
    exact KernelOperator.normalizedSetL2_inner K hK i.val
  have hzz : 0 ≤ B z z := by
    change 0 ≤ B ((μ.real K)⁻¹ • indicatorVector K hK)
      ((μ.real K)⁻¹ • indicatorVector K hK)
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr measureReal_nonneg)
      (mul_nonneg (inv_nonneg.mpr measureReal_nonneg)
        (schurForm_indicator_nonnegative K hK hW))
  have heb : B bh e = ν := (hsym bh e).trans hbe
  have hea : B e a = ν := S.schurForm_constant_head i hW
  have hez : B e z = ν := by
    rw [schurForm_constant hW, KernelOperator.normalizedSetL2_integral K hK hk]
    ring
  have hab : B a bh = 0 := (hsym a bh).trans hba
  have hzb : B z bh = 0 := (hsym z bh).trans hbz
  have hff : B f f = -ν := by
    simp only [f, map_sub, LinearMap.sub_apply]
    rw [hbb, heb, hbe, hee]
    ring
  have hfwI : B f wI = 0 := by
    simp only [f, wI, map_sub, map_smul, LinearMap.sub_apply, smul_eq_mul]
    rw [hbb, hba, hbe, hea]
    ring
  have hfwK : B f wK = 0 := by
    simp only [f, wK, map_sub, map_smul, LinearMap.sub_apply, smul_eq_mul]
    rw [hbb, hbz, hbe, hez]
    ring
  have hwIwI : B wI wI = 0 := by
    simp only [wI, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [hbb, hba, hab, haa]
    ring
  have hwIwK : B wI wK = A * E := by
    simp only [wI, wK, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [hbb, hbz, hab, haz]
    field_simp [ne_of_gt hk']
    ring
  have hwKwK : B wK wK = k ^ 2 * B z z := by
    simp only [wK, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [hbb, hbz, hzb]
    ring
  have heA : ⟪e, a⟫ = 1 := by
    rw [KernelOperator.inner_constant_one]
    exact KernelOperator.normalizedSetL2_integral I hI (S.hfibers i.val i.property).2.1
  have heB : ⟪e, bh⟫ = 1 := by
    rw [KernelOperator.inner_constant_one]
    exact KernelOperator.normalizedSetL2_integral _ _ (S.hfibers p.val p.property).2.1
  have heZ : ⟪e, z⟫ = 1 := by
    rw [KernelOperator.inner_constant_one]
    exact KernelOperator.normalizedSetL2_integral K hK hk
  have heeInner : ⟪e, e⟫ = 1 := by
    change ⟪Lp.const 2 μ (1 : ℝ), Lp.const 2 μ (1 : ℝ)⟫ = 1
    rw [real_inner_self_eq_norm_sq, KernelOperator.constant_one_norm]
    norm_num
  have hfbound : f ∈ KernelOperator.boundedL2Submodule μ :=
    (KernelOperator.boundedL2Submodule μ).sub_mem
      (KernelOperator.normalizedSetL2_bounded _ _)
      Variation.constant_one_bounded
  have hwIbound : wI ∈ KernelOperator.boundedL2Submodule μ :=
    (KernelOperator.boundedL2Submodule μ).smul_mem A
      ((KernelOperator.boundedL2Submodule μ).sub_mem
        (KernelOperator.normalizedSetL2_bounded _ _)
        (KernelOperator.normalizedSetL2_bounded _ _))
  have hwKbound : wK ∈ KernelOperator.boundedL2Submodule μ :=
    (KernelOperator.boundedL2Submodule μ).smul_mem k
      ((KernelOperator.boundedL2Submodule μ).sub_mem
        (KernelOperator.normalizedSetL2_bounded _ _)
        (KernelOperator.normalizedSetL2_bounded _ _))
  have hall : ∀ y w : ℝ, k ^ 2 * B z z + 2 * y * A * E - w ^ 2 * ν ≤
      C * (DK + y * A * k + w * D) ^ 2 := by
    intro y w
    let v := wK + y • wI + w • f
    have hvmean : (∫ x, v x ∂μ) = 0 := by
      rw [← KernelOperator.inner_constant_one]
      simp only [v, wK, wI, f, inner_sub_right, inner_add_right,
        real_inner_smul_right]
      rw [heA, heB, heZ, heeInner]
      ring
    have hvbound : v ∈ KernelOperator.boundedL2Submodule μ :=
      (KernelOperator.boundedL2Submodule μ).add_mem
        ((KernelOperator.boundedL2Submodule μ).add_mem hwKbound
          ((KernelOperator.boundedL2Submodule μ).smul_mem y hwIbound))
        ((KernelOperator.boundedL2Submodule μ).smul_mem w hfbound)
    have hvdegree : ⟪g, v⟫ = -(DK + y * A * k + w * D) := by
      simp only [v, wK, wI, f, inner_sub_right, inner_add_right,
        real_inner_smul_right]
      have hgai : ⟪g, a⟫ = ⟪g, bh⟫ + k := by
        rw [hgi, hgp, hdegI, hdegP]
        ring
      have hgee : ⟪g, e⟫ = ⟪g, bh⟫ + D := by
        rw [hge, hgp, hdegP]
        ring
      rw [hgai, hgee]
      ring
    have hQ := hcurv v hvbound hvmean
    change B v v ≤ C * ⟪g, v⟫ ^ 2 at hQ
    have hwKwI : B wK wI = B wI wK := hsym wK wI
    have hwIf : B wI f = 0 := (hsym wI f).trans hfwI
    have hwKf : B wK f = 0 := (hsym wK f).trans hfwK
    have hQexp : B v v = k ^ 2 * B z z + 2 * y * A * E - w ^ 2 * ν := by
      simp only [v, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul]
      rw [hwKwK, hwIwK, hwKwI, hwIwI, hfwI, hfwK, hwIf, hwKf, hff, hwIwK]
      ring
    rw [hQexp, hvdegree] at hQ
    simpa only [neg_sq] using hQ
  have hscalar := MiddleE2PrivateScalar.curvature_schur hA hk' hν hC hDKupper hE
    (mul_nonneg (sq_nonneg k) hzz) hall
  simpa only [D, A, b, k, I, P, K, ν] using hscalar

end Erdos1017.CappedModel.SelectedHighLowStructure
