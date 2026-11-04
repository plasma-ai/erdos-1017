module

public import Erdos1017.Exclusions.E2.Middle.SelectedMiddlePrivateFailedInsertion
public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleOffPairDominance
public import Erdos1017.Exclusions.Common.Saturation.SelectedSaturatedPairStrictScore
public import Erdos1017.Exclusions.Common.Saturation.SelectedSaturatedHeadScore

/-!
# Saturated-pair score on the private sector

With the unique saturated pair `U, V`, a common peak `I` private against `U`,
and the entire hole `K = (I ∪ U)ᶜ \ N(U)`, the saturated-pair score inequality
on the private sector follows (`middle_saturated_private_score`), using the
whole-atom triangle (`ae_atom_triangle`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- The original whole-atom triangle. For physically joined whole atoms
`r, s`, the averaged `s`-star is a constant `κ` on `r`, and almost every
common neighbor `z` obeys `κ + Y(ρ_r, z) + Y(ρ_s, z) ≤ 1`. The clique test is
licensed by pair regularity of the same original model. -/
theorem ae_atom_triangle (S : SelectedHighLowStructure W m) (r s : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hjoin : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → S.ρ p.2 = s.val →
      PhysicalRepresentative.adjacency W m p.1 p.2 = true) :
    ∃ κ : ℝ, (∀ᵐ x ∂μ, S.ρ x = r.val → S.rootChargeRow s x = κ) ∧
      ∀ᵐ z ∂μ, z ∈ S.rootNeighborhood r → z ∈ S.rootNeighborhood s →
        κ + S.rootChargeRow r z + S.rootChargeRow s z ≤ 1 := by
  let G : Ω × Ω → Bool := Function.uncurry (PhysicalRepresentative.adjacency W m)
  let Y : Ω × Ω → ℝ := Function.uncurry (PhysicalRepresentative.charge W m)
  have hG : Measurable G := PhysicalRepresentative.measurable_adjacency W m
  have hY : Measurable Y := PhysicalRepresentative.measurable_charge W m
  have hYb : ∀ z, |Y z| ≤ 3 := fun z => PhysicalRepresentative.charge_bound W m z.1 z.2
  have htest : ∀ k, 2 ≤ k → ∀ᵐ v ∂Measure.pi (fun _ : Fin k => μ),
      PhysicalCliqueRepresentative.Clique G v → PhysicalPrimal.charge Y v ≤ 1 := by
    intro k _
    filter_upwards [PhysicalRepresentative.full_feasible W hW.full m
      (hW.strict_gap_structure hd hgap).strict_support hW.deterministic k] with v hv hc
    change PhysicalPrimal.charge (Function.uncurry
      (PhysicalRepresentative.charge W m)) v ≤ 1
    rw [MultipartiteHeadPrice.physicalCharge_eq_tupleCharge]
    exact hv hc
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving
  have hreg := PhysicalCliqueRepresentative.ae_pairRegular μ hG hY 3 hYb
  have hQ : ∀ᵐ p ∂μ.prod μ,
      PhysicalCliqueRepresentative.PairRegular μ G Y p ∧
      PhysicalCliqueRepresentative.PairRegular μ G Y p.swap ∧
      (S.ρ p.1 = r.val → (PhysicalRepresentative.adjacency W m p.1 p.2 = true ↔
        p.2 ∈ S.rootNeighborhood r)) ∧
      (S.ρ p.1 = s.val → (PhysicalRepresentative.adjacency W m p.1 p.2 = true ↔
        p.2 ∈ S.rootNeighborhood s)) ∧
      (S.ρ p.1 = r.val → PhysicalRepresentative.charge W m p.1 p.2 = S.rootChargeRow r p.2) ∧
      (S.ρ p.1 = s.val → PhysicalRepresentative.charge W m p.1 p.2 = S.rootChargeRow s p.2) ∧
      (S.ρ p.1 = r.val → S.ρ p.2 = s.val →
        PhysicalRepresentative.adjacency W m p.1 p.2 = true) := by
    filter_upwards [hreg, hswap.ae hreg, S.ae_root_adjacency r hW hd hgap,
      S.ae_root_adjacency s hW hd hgap, S.ae_root_charge r hW hd hgap,
      S.ae_root_charge s hW hd hgap, hjoin] with p h1 h2 h3 h4 h5 h6 h7
    exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  have hsec := Measure.ae_ae_of_ae_prod hQ
  have hsec' := Measure.ae_ae_of_ae_prod (hswap.ae hQ)
  obtain ⟨x, hx, hxsec⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers r.val r.property).2.1.ne' (ae_restrict_of_ae hsec)
  obtain ⟨y, hy, hysec, hysec', hxy⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers s.val s.property).2.1.ne'
    ((ae_restrict_of_ae hsec).and ((ae_restrict_of_ae hsec').and (ae_restrict_of_ae hxsec)))
  refine ⟨S.rootChargeRow r y, ?_, ?_⟩
  · filter_upwards [hysec', hysec] with x' h1 h2 hx'
    have e1 : PhysicalRepresentative.charge W m x' y = S.rootChargeRow r y :=
      h1.2.2.2.2.1 hx'
    have e2 : PhysicalRepresentative.charge W m y x' = S.rootChargeRow s x' :=
      h2.2.2.2.2.2.1 hy
    rw [← e2, PhysicalRepresentative.charge_symm, e1]
  · filter_upwards [hxsec, hysec] with z hxz hyz hzr hzs
    have hxyA : PhysicalRepresentative.adjacency W m x y = true := hxy.2.2.2.2.2.2 hx hy
    have hxzA : PhysicalRepresentative.adjacency W m x z = true := (hxz.2.2.1 hx).mpr hzr
    have hyzA : PhysicalRepresentative.adjacency W m y z = true := (hyz.2.2.2.1 hy).mpr hzs
    have hyxA : PhysicalRepresentative.adjacency W m y x = true := by
      rw [PhysicalRepresentative.adjacency_symm]
      exact hxyA
    have hzxA : PhysicalRepresentative.adjacency W m z x = true := by
      rw [PhysicalRepresentative.adjacency_symm]
      exact hxzA
    have hzyA : PhysicalRepresentative.adjacency W m z y = true := by
      rw [PhysicalRepresentative.adjacency_symm]
      exact hyzA
    have hclique : PhysicalCliqueRepresentative.Clique G ![x, y, z] := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp <;>
        first | exact hxyA | exact hyxA | exact hxzA | exact hzxA | exact hyzA |
          exact hzyA | exact False.elim (hab rfl)
    have hregular : ∀ a b : Fin 3, a ≠ b →
        PhysicalCliqueRepresentative.PairRegular μ G Y (![x, y, z] a, ![x, y, z] b) := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp <;>
        first | exact hxy.1 | exact hxy.2.1 | exact hxz.1 | exact hxz.2.1 | exact hyz.1 |
          exact hyz.2.1 | exact False.elim (hab rfl)
    have hle := PhysicalCliqueRepresentative.charge_le_of_pairRegular μ hG hY 3
      (by norm_num) hYb htest 3 ![x, y, z] hclique hregular
    rw [PhysicalTriangleExposure.charge_three Y (PhysicalRepresentative.charge_symm W m)] at hle
    have e1 : Y (x, y) = S.rootChargeRow r y := hxy.2.2.2.2.1 hx
    have e2 : Y (x, z) = S.rootChargeRow r z := hxz.2.2.2.2.1 hx
    have e3 : Y (y, z) = S.rootChargeRow s z := hyz.2.2.2.2.2.1 hy
    linarith

private theorem ae_rootChargeRow_eq_row_plus (S : SelectedHighLowStructure W m) (r : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    ∀ᵐ y ∂μ, S.rootChargeRow r y =
      r.val y + m * (if 0 < r.val y then 1 else 0) := by
  let Ir : Set Ω := {x | S.ρ x = r.val}
  have hIrpos : 0 < μ Ir := (S.hfibers r.val r.property).2.1
  have hrows : ∀ᵐ x ∂μ.restrict Ir,
      chargeKernel W x =ᵐ[μ]
        fun y => r.val y + m * (if 0 < r.val y then 1 else 0) :=
    (S.hfibers r.val r.property).2.2.2.rows.mono (fun _ hx => hx.2.2)
  have hs := hW.strict_gap_structure hd hgap
  have hpair : ∀ᵐ q ∂μ.prod μ, q.1 ∈ Ir →
      PhysicalRepresentative.charge W m q.1 q.2 = S.rootChargeRow r q.2 ∧
      PhysicalRepresentative.charge W m q.1 q.2 = chargeKernel W q.1 q.2 := by
    filter_upwards [S.ae_root_charge r hW hd hgap,
      PhysicalRepresentative.charge_ae_eq W m hs.strict_support] with q hroot hp hIr
    exact ⟨hroot hIr, hp⟩
  have hsections := Measure.ae_ae_of_ae_prod hpair
  obtain ⟨x, hxIr, hxrows, hxsection⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hIrpos.ne'
      (hrows.and (ae_restrict_of_ae hsections))
  filter_upwards [hxrows, hxsection] with y hy hp
  exact (hp hxIr).1.symm.trans ((hp hxIr).2.trans hy)

/-- The saturated-pair score on the private sector. With the unique
saturated pair `U, V`, a common peak `I` private against `U`, and the
entire hole `K = (I ∪ U)ᶜ \ N(U)`, the score `1 - m - M(U,·) - M(V,·)` is
nonnegative, equals `1 - κ` on `I` and is at least `κ` on `K` whenever the
`I`-stars on `K` are nonnegative. Its total is `Δ = 1 - m - 2ν`. -/
theorem middle_saturated_private_score (S : SelectedHighLowStructure W m)
    (u v i : S.I) (hpair : S.IsSaturatedAtomPair u v) (hiu : i ≠ u) (hiv : i ≠ v)
    (hnoui : ¬S.IsSaturatedAtomPair u i) (hnovi : ¬S.IsSaturatedAtomPair v i)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (hell : -m < 1)
    (hprivate : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      adjacencyKernel W z.1 z.2 = if S.ρ z.2 = i.val ∨ S.ρ z.2 = u.val then 0 else 1)
    (hstars : ∀ᵐ x ∂μ.restrict (({x | S.ρ x = i.val} ∪ {x | S.ρ x = u.val})ᶜ \
      S.rootNeighborhood u), 0 ≤ S.rootChargeRow i x) :
    ∃ κ : ℝ, m ≤ κ ∧ κ < 1 ∧
      μ.real {x | S.ρ x = i.val} * (1 - κ) +
        μ.real (({x | S.ρ x = i.val} ∪ {x | S.ρ x = u.val})ᶜ \ S.rootNeighborhood u) * κ ≤
      1 - m - 2 * (2 * (c - m * d)) := by
  let I := {x | S.ρ x = i.val}
  let U := {x | S.ρ x = u.val}
  let K := (I ∪ U)ᶜ \ S.rootNeighborhood u
  have hIm : MeasurableSet I := (S.hfibers i.val i.property).1
  have hUm : MeasurableSet U := (S.hfibers u.val u.property).1
  have hKm : MeasurableSet K := (hIm.union hUm).compl.diff (S.measurableSet_rootNeighborhood u)
  have hmneg : m < 0 := (hW.strict_gap_structure hd hgap).multiplier_neg
  have hNiff := S.ae_private_rootNeighborhood_iff i u hW hd hgap hprivate
  have hjoin : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = i.val → S.ρ p.2 = v.val →
      PhysicalRepresentative.adjacency W m p.1 p.2 = true := by
    filter_upwards [S.ae_root_adjacency i hW hd hgap,
      Measure.quasiMeasurePreserving_snd.ae hNiff] with p hp hN hpi hpv
    apply (hp hpi).mpr
    exact hN.mpr ⟨fun h => hiv (Subtype.ext (h.symm.trans hpv)),
      fun h => hpair.1 (Subtype.ext (h.symm.trans hpv))⟩
  obtain ⟨κ, hκconst, htri⟩ := S.ae_atom_triangle i v hW hd hgap hjoin
  have hINv := S.ae_private_root_mem_atomNeighborhood i u v (fun h => hiv h.symm)
    (fun h => hpair.1 h.symm) hW hd hgap hprivate
  have hINu := S.ae_second_root_not_mem_atomNeighborhood i u hW hd hgap
    ((ae_restrict_iff' hUm).mpr (hNiff.mono (fun x hx hxU hxN => (hx.mp hxN).2 hxU)))
  have hrpv := ae_rootChargeRow_eq_row_plus S v hW hd hgap
  have hrpi := ae_rootChargeRow_eq_row_plus S i hW hd hgap
  -- The score on the private peak.
  have hIrow : ∀ᵐ x ∂μ, S.ρ x = i.val → u.val x = 0 ∧ v.val x = κ - m := by
    filter_upwards [hκconst, hINv, hINu, hrpv, S.ae_rootNeighborhood_iff u,
      S.ae_rootNeighborhood_iff v, S.ae_whole_row_nonneg u hW] with x hκ hNv hNu hrp hiffu
      hiffv hnnu hx
    have hvpos : 0 < v.val x := hiffv.mp (hNv hx)
    refine ⟨le_antisymm (le_of_not_gt (fun h => hNu hx (hiffu.mpr h))) hnnu, ?_⟩
    simp only [hvpos, ↓reduceIte, mul_one] at hrp
    linarith [hκ hx]
  obtain ⟨x0, hx0, hstrict0, hrow0, hnn0⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers i.val i.property).2.1.ne'
    ((hpair.score_lt_on_other_atom i (fun h => hiu h.symm) (fun h => hiv h.symm) hnoui hnovi
      hW hd hgap hell).and ((ae_restrict_of_ae hIrow).and
        (ae_restrict_of_ae (S.ae_whole_row_nonneg v hW))))
  have hrow0' := hrow0 hx0
  have hκ1 : κ < 1 := by linarith [hrow0'.1, hrow0'.2]
  have hmκ : m ≤ κ := by linarith [hrow0'.2]
  -- The score on the entire hole.
  have hKpt : ∀ᵐ z ∂μ.restrict K, κ ≤ 1 - m - u.val z - v.val z := by
    filter_upwards [hstars, ae_restrict_mem hKm, ae_restrict_of_ae htri,
      ae_restrict_of_ae hNiff, ae_restrict_of_ae hrpi, ae_restrict_of_ae hrpv,
      ae_restrict_of_ae (S.ae_rootNeighborhood_iff u),
      ae_restrict_of_ae (S.ae_rootNeighborhood_iff i),
      ae_restrict_of_ae (S.ae_rootNeighborhood_iff v),
      ae_restrict_of_ae (S.ae_whole_row_nonneg u hW),
      ae_restrict_of_ae (S.ae_whole_row_nonneg v hW)] with z hst hzK htz hNi hpi hpv hiffu
      hiffi hiffv hnnu hnnv
    have hzNi : z ∈ S.rootNeighborhood i :=
      hNi.mpr ⟨fun h => hzK.1 (Or.inl h), fun h => hzK.1 (Or.inr h)⟩
    have hu0 : u.val z = 0 := le_antisymm (le_of_not_gt (fun h => hzK.2 (hiffu.mpr h))) hnnu
    have hipos : 0 < i.val z := hiffi.mp hzNi
    simp only [hipos, ↓reduceIte, mul_one] at hpi
    by_cases hzv : z ∈ S.rootNeighborhood v
    · have hvpos : 0 < v.val z := hiffv.mp hzv
      simp only [hvpos, ↓reduceIte, mul_one] at hpv
      have h := htz hzNi hzv
      linarith
    · have hv0 : v.val z = 0 := le_antisymm (le_of_not_gt (fun h => hzv (hiffv.mpr h))) hnnv
      linarith
  -- Integrate against the saturated score total.
  have hscore := S.ae_saturated_head_score_le hW hd hgap hell u v hpair.1 hpair.2
  have hpoint : ∀ᵐ x ∂μ, I.indicator (fun _ => 1 - κ) x + K.indicator (fun _ => κ) x ≤
      1 - m - u.val x - v.val x := by
    filter_upwards [hscore, hIrow, (ae_restrict_iff' hKm).mp hKpt] with x hs hI hK
    by_cases hxI : x ∈ I
    · have hxK : x ∉ K := fun h => h.1 (Or.inl hxI)
      rw [indicator_of_mem hxI, indicator_of_notMem hxK]
      obtain ⟨h1, h2⟩ := hI hxI
      linarith
    · rw [indicator_of_notMem hxI, zero_add]
      by_cases hxK : x ∈ K
      · rw [indicator_of_mem hxK]
        exact hK hxK
      · rw [indicator_of_notMem hxK]
        linarith
  have hu : Integrable (u.val : Ω → ℝ) μ := (Lp.memLp u.val).integrable (by norm_num)
  have hv : Integrable (v.val : Ω → ℝ) μ := (Lp.memLp v.val).integrable (by norm_num)
  have hsI : Integrable (fun x => 1 - m - (u.val : Ω → ℝ) x - (v.val : Ω → ℝ) x) μ :=
    ((integrable_const (1 - m)).sub hu).sub hv
  have hfI : Integrable (fun x => I.indicator (fun _ => 1 - κ) x +
      K.indicator (fun _ => κ) x) μ :=
    ((integrable_const _).indicator hIm).add ((integrable_const _).indicator hKm)
  have hle := integral_mono_ae hfI hsI hpoint
  rw [integral_add ((integrable_const _).indicator hIm) ((integrable_const _).indicator hKm),
    integral_indicator_const _ hIm, integral_indicator_const _ hKm,
    S.integral_saturated_score_deficit u v hW, smul_eq_mul, smul_eq_mul] at hle
  exact ⟨κ, hmκ, hκ1, hle⟩

end Erdos1017.CappedModel.SelectedHighLowStructure
