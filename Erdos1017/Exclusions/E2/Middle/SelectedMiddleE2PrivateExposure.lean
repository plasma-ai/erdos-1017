module

public import Erdos1017.Exclusions.Common.Private.SelectedPrivatePositiveStars

/-!
# Triangle exposure of private root stars

A tight triangle of the selected model exposes every private root star in the
large private sector `3A + b > 1`, with a separate statement for a leaf in the
second whole fiber's hole (`ae_permuted_private_triangle_exposure_sector`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

/-- The integrated insertion calculation of
`ae_permuted_private_triangle_exposure`, retaining the signed contribution
of the private second fiber. -/
private theorem triangle_integral_le_private_cover
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (G : Ω × Ω → Bool) (hG : Measurable G)
    (Y : Ω × Ω → ℝ) (hY : Measurable Y) (B : ℝ)
    (hbound : ∀ p, |Y p| ≤ B)
    (ell ν : ℝ) (v : Fin 3 → Ω) (C : Set Ω) (hC : MeasurableSet C)
    (hmean : ∀ i : Fin 3, (∫ z, Y (z, v i) +
      ell * (if G (z, v i) then 1 else 0) ∂μ) = ν)
    (hinsertion : ∀ᵐ z ∂μ,
      Y (z, v 0) + Y (z, v 1) + Y (z, v 2) -
        ell * ((if G (z, v 0) then 0 else 1) +
          (if G (z, v 1) then 0 else 1) +
          (if G (z, v 2) then 0 else 1)) ≤
          TriangleInsertion.majorant ell (Y (v 0, v 1) + Y (v 0, v 2))
            (Y (v 0, v 1) + Y (v 1, v 2))
            (Y (v 0, v 2) + Y (v 1, v 2))
            (G (z, v 0)) (G (z, v 1)) (G (z, v 2)))
    (hcover : ∀ᵐ z ∂μ,
      TriangleInsertion.majorant ell
        (Y (v 0, v 1) + Y (v 0, v 2))
        (Y (v 0, v 1) + Y (v 1, v 2))
        (Y (v 0, v 2) + Y (v 1, v 2))
        (G (z, v 0)) (G (z, v 1)) (G (z, v 2)) ≤
          C.indicator (fun _ => Y (v 0, v 1) + Y (v 0, v 2) - ell) z +
            {z | G (z, v 1) = false}.indicator
              (fun _ => max (1 - ell - Y (v 0, v 2)) 0) z +
            {z | G (z, v 2) = false}.indicator
              (fun _ => 1 - ell - Y (v 0, v 1)) z) :
    3 * (ν - ell) ≤
      μ.real C * (Y (v 0, v 1) + Y (v 0, v 2) - ell) +
        μ.real {z | G (z, v 1) = false} *
          max (1 - ell - Y (v 0, v 2)) 0 +
        μ.real {z | G (z, v 2) = false} *
          (1 - ell - Y (v 0, v 1)) := by
  let F1 := {z | G (z, v 1) = false}
  let F2 := {z | G (z, v 2) = false}
  have hF1 : MeasurableSet F1 := (hG.comp (measurable_id.prodMk measurable_const))
    (measurableSet_singleton false)
  have hF2 : MeasurableSet F2 := (hG.comp (measurable_id.prodMk measurable_const))
    (measurableSet_singleton false)
  let L := fun z => Y (z, v 0) + Y (z, v 1) + Y (z, v 2) -
    ell * ((if G (z, v 0) then 0 else 1) +
      (if G (z, v 1) then 0 else 1) +
      (if G (z, v 2) then 0 else 1))
  let R := fun z => C.indicator
    (fun _ => Y (v 0, v 1) + Y (v 0, v 2) - ell) z +
    F1.indicator (fun _ => max (1 - ell - Y (v 0, v 2)) 0) z +
    F2.indicator (fun _ => 1 - ell - Y (v 0, v 1)) z
  have hle : L ≤ᵐ[μ] R := by
    filter_upwards [hinsertion, hcover] with z hi hc
    exact hi.trans hc
  let f := fun i : Fin 3 => fun z => Y (z, v i) +
    ell * (if G (z, v i) then 1 else 0)
  have hf (i : Fin 3) : Integrable (f i) μ := by
    have hy : Integrable (fun z => Y (z, v i)) μ := Integrable.of_bound
      (hY.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable B
      (Eventually.of_forall (fun z => by
        simpa only [Real.norm_eq_abs] using hbound (z, v i)))
    have hg : Integrable (fun z => if G (z, v i) then (1 : ℝ) else 0) μ :=
      Integrable.of_bound
        (Measurable.ite ((hG.comp (measurable_id.prodMk measurable_const))
          (measurableSet_singleton true)) measurable_const measurable_const).aestronglyMeasurable
        1 (Eventually.of_forall (fun z => by cases G (z, v i) <;> norm_num))
    exact hy.add (hg.const_mul ell)
  have hL : L = fun z => f 0 z + f 1 z + f 2 z - 3 * ell := by
    funext z
    cases h0 : G (z, v 0) <;> cases h1 : G (z, v 1) <;>
      cases h2 : G (z, v 2) <;>
      simp [L, f, h0, h1, h2] <;> ring
  have hiL : Integrable L μ := by
    rw [hL]
    exact (((hf 0).add (hf 1)).add (hf 2)).sub (integrable_const (3 * ell))
  have hmeanL : (∫ z, L z ∂μ) = 3 * (ν - ell) := by
    rw [hL, integral_sub, integral_add, integral_add]
    change (∫ z, f 0 z ∂μ) + (∫ z, f 1 z ∂μ) +
      (∫ z, f 2 z ∂μ) - _ = _
    rw [show (∫ z, f 0 z ∂μ) = ν from hmean 0,
      show (∫ z, f 1 z ∂μ) = ν from hmean 1,
      show (∫ z, f 2 z ∂μ) = ν from hmean 2]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    ring
    all_goals first
      | exact integrable_const _
      | exact hf 0
      | exact hf 1
      | exact hf 2
      | exact (hf 0).add (hf 1)
      | exact ((hf 0).add (hf 1)).add (hf 2)
  have hi0 : Integrable (C.indicator
      (fun _ : Ω => Y (v 0, v 1) + Y (v 0, v 2) - ell)) μ :=
    (integrable_const _).indicator hC
  have hi1 : Integrable (F1.indicator
      (fun _ : Ω => max (1 - ell - Y (v 0, v 2)) 0)) μ :=
    (integrable_const _).indicator hF1
  have hi2 : Integrable (F2.indicator
      (fun _ : Ω => 1 - ell - Y (v 0, v 1))) μ :=
    (integrable_const _).indicator hF2
  have hiR : Integrable R μ := (hi0.add hi1).add hi2
  have hmeanR : (∫ z, R z ∂μ) =
      μ.real C * (Y (v 0, v 1) + Y (v 0, v 2) - ell) +
        μ.real F1 * max (1 - ell - Y (v 0, v 2)) 0 +
        μ.real F2 * (1 - ell - Y (v 0, v 1)) := by
    rw [show R = fun z => C.indicator
      (fun _ => Y (v 0, v 1) + Y (v 0, v 2) - ell) z +
      F1.indicator (fun _ => max (1 - ell - Y (v 0, v 2)) 0) z +
      F2.indicator (fun _ => 1 - ell - Y (v 0, v 1)) z from rfl,
      integral_add, integral_add,
      integral_indicator hC, integral_indicator hF1, integral_indicator hF2]
    simp only [setIntegral_const, smul_eq_mul]
    all_goals first
      | exact hi0
      | exact hi1
      | exact hi2
      | exact hi0.add hi1
  have hh := integral_mono_ae hiL hiR hle
  rw [hmeanL, hmeanR] at hh
  exact hh

/-- The two-neighbor case of the private sector: its missing capacity is
`R_N = 1 - 2A - b`, which is at most the singleton mass `A + b` under
`3A + b > 1`. The margin is the separate sector margin, not `A > 1/3`. -/
private theorem private_NN_root_charge_pos
    (A b ell ν u v F1 F2 : ℝ)
    (hb : 0 ≤ b) (hsector : 1 < 3 * A + b)
    (hell : ell ∈ Ioo (1 / 2 : ℝ) 1)
    (hNN : (1 - ell) * (1 - A) < 3 * (ν - ell))
    (hv : v ≤ 1) (hF1 : F1 ≤ 1 - 2 * A - b)
    (hF2 : F2 ≤ 1 - 2 * A - b)
    (hint : 3 * (ν - ell) ≤
      (A + b) * (u + v - ell) +
        F1 * max (1 - ell - v) 0 + F2 * (1 - ell - u)) :
    0 < u := by
  by_contra hu
  have hu' : u ≤ 0 := le_of_not_gt hu
  have hR : 1 - 2 * A - b ≤ A + b := by linarith
  have hα : 0 ≤ A + b := by linarith
  have hc1 := mul_le_mul_of_nonneg_right hF1 (le_max_right (1 - ell - v) 0)
  have hc2 := mul_le_mul_of_nonneg_right hF2
    (show 0 ≤ 1 - ell - u by linarith [hell.2, hu'])
  have hcap := TriangleInsertion.private_NN_star_capacity hα hR
    (show 0 ≤ ell by linarith [hell.1]) hu' hv
  nlinarith

private theorem private_K_root_charge_gt
    (A ell ν u v F1 F2 : ℝ)
    (hA : 0 ≤ A) (hell : 0 ≤ ell)
    (hmargin : 2 * (1 - ell) * A < 3 * (ν - ell))
    (hv : v ≤ 1)
    (hF1 : F1 * max (1 - ell - v) 0 ≤
      A * max (1 - ell - v) 0)
    (hF2 : F2 * (1 - ell - u) ≤ A * (1 - ell - u))
    (hint : 3 * (ν - ell) ≤
      A * (u + v - ell) +
        F1 * max (1 - ell - v) 0 + F2 * (1 - ell - u)) :
    1 - ell < u := by
  by_contra hu
  have hu' : u ≤ 1 - ell := le_of_not_gt hu
  have hcap := TriangleInsertion.private_K_star_capacity
    (A := A) (ell := ell) (u := u) (v := v) hA hell hv
  nlinarith

private theorem majorant_le_private_second_K_cover
    (ell u v : ℝ) (b0 b1 b2 : Bool)
    (i p : Prop) [Decidable i] [Decidable p]
    (h0 : b0 = false ↔ i ∨ p)
    (hI1 : i → b1 = true) (hI2 : i → b2 = true)
    (hP2 : p → b2 = false)
    (hell : (1 / 2 : ℝ) ≤ ell) (hu : u ≤ 0) :
    TriangleInsertion.majorant ell (u + v) (1 - v) (1 - u) b0 b1 b2 ≤
      (if i then u + v - ell else 0) +
        (if b1 = false then max (1 - ell - v) 0 else 0) +
        (if b2 = false then 1 - ell - u else 0) := by
  by_cases hi : i
  · have hb0 := h0.mpr (Or.inl hi)
    simp [TriangleInsertion.majorant, hi, hb0, hI1 hi, hI2 hi]
  · by_cases hp : p
    · have hb0 := h0.mpr (Or.inr hp)
      have hb2 := hP2 hp
      cases b1 <;>
        simp [TriangleInsertion.majorant, hi, hb0, hb2] <;>
        linarith [le_max_right (1 - ell - v) 0]
    · have hb0 : b0 = true := by cases b0 <;> simp_all
      cases b1 <;> cases b2 <;>
        simp only [TriangleInsertion.majorant, hb0, hi,
          Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte,
          zero_add, add_zero] <;>
        linarith [le_max_left (1 - ell - v) 0,
          le_max_right (1 - ell - v) 0]

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [IsProbabilityMeasure μ]
  [NullSingletonClass μ] [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem ae_all_pairs_private {n : ℕ} (τ : Measure (Fin n → Ω))
    (hpairs : ∀ a b, a ≠ b → τ.map (fun v => (v a, v b)) ≪ μ.prod μ)
    (P : Ω × Ω → Prop) (hP : ∀ᵐ p ∂μ.prod μ, P p) :
    ∀ᵐ v ∂τ, ∀ a b, a ≠ b → P (v a, v b) := by
  simp only [ae_all_iff]
  intro a b hab
  exact ae_of_ae_map ((measurable_pi_apply a).prodMk
    (measurable_pi_apply b)).aemeasurable ((hpairs a b hab).ae_le hP)

omit [StandardBorelSpace Ω] [MeasurableEq Ω]
  [NullSingletonClass μ] [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
private theorem ae_all_coordinates_private {n : ℕ} (hn : 2 ≤ n)
    (τ : Measure (Fin n → Ω))
    (hpairs : ∀ a b, a ≠ b → τ.map (fun v => (v a, v b)) ≪ μ.prod μ)
    (P : Ω → Prop) (hP : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ v ∂τ, ∀ a, P (v a) := by
  simp only [ae_all_iff]
  intro a
  exact ae_of_ae_map (measurable_pi_apply a).aemeasurable
    ((PhysicalCliqueRepresentative.coordinate_absolutelyContinuous_of_pairs
      μ hn τ hpairs a).ae_le hP)

private theorem ae_private_physical_columns
    (S : SelectedHighLowStructure W m) (i p : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hprivate : ∀ᵐ q ∂μ.prod μ, S.ρ q.1 = i.val →
      adjacencyKernel W q.1 q.2 =
        if S.ρ q.2 = i.val ∨ S.ρ q.2 = p.val then 0 else 1) :
    ∀ᵐ x ∂μ,
      (S.ρ x = i.val → ∀ᵐ z ∂μ,
        PhysicalRepresentative.adjacency W m z x = false ↔
          S.ρ z = i.val ∨ S.ρ z = p.val) ∧
      (S.ρ x ≠ i.val ∧ S.ρ x ≠ p.val → ∀ᵐ z ∂μ,
        S.ρ z = i.val → PhysicalRepresentative.adjacency W m z x = true) ∧
      (x ∈ S.rootNeighborhood p → ∀ᵐ z ∂μ,
        S.ρ z = p.val → PhysicalRepresentative.adjacency W m z x = true) ∧
      (x ∉ S.rootNeighborhood p → ∀ᵐ z ∂μ,
        S.ρ z = p.val → PhysicalRepresentative.adjacency W m z x = false) := by
  have hroot : ∀ᵐ q ∂μ.prod μ, S.ρ q.1 = i.val →
      (PhysicalRepresentative.adjacency W m q.1 q.2 = false ↔
        S.ρ q.2 = i.val ∨ S.ρ q.2 = p.val) := by
    filter_upwards [S.ae_root_adjacency i hW hd hgap,
      Measure.quasiMeasurePreserving_snd.ae
        (S.ae_private_rootNeighborhood_iff i p hW hd hgap hprivate)]
      with q hg hmem hi
    have he : PhysicalRepresentative.adjacency W m q.1 q.2 = true ↔
        S.ρ q.2 ≠ i.val ∧ S.ρ q.2 ≠ p.val := (hg hi).trans hmem
    constructor
    · intro hfalse
      by_contra hnot
      have hn : S.ρ q.2 ≠ i.val ∧ S.ρ q.2 ≠ p.val := by
        simpa only [not_or, not_not] using hnot
      have ht := he.mpr hn
      rw [hfalse] at ht
      contradiction
    · intro hor
      cases hh : PhysicalRepresentative.adjacency W m q.1 q.2 with
      | false => rfl
      | true =>
        have hn := he.mp hh
        exact False.elim (hor.elim hn.1 hn.2)
  have hsecond : ∀ᵐ q ∂μ.prod μ, S.ρ q.2 = p.val →
      (PhysicalRepresentative.adjacency W m q.2 q.1 = true ↔
        q.1 ∈ S.rootNeighborhood p) := by
    have hsw := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
      (S.ae_root_adjacency p hW hd hgap)
    filter_upwards [hsw] with q hq hp
    exact hq hp
  filter_upwards [Measure.ae_ae_of_ae_prod hroot,
    Measure.ae_ae_of_ae_prod ((Measure.measurePreserving_swap
      (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hroot),
    Measure.ae_ae_of_ae_prod hsecond] with x hr hi hp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hi
    exact hr.mono (fun z hz => by
      have hh := hz hi
      rw [PhysicalRepresentative.adjacency_symm W m x z] at hh
      exact hh)
  · intro hx
    exact hi.mono (fun z hz hzI => by
      have hh := hz hzI
      change PhysicalRepresentative.adjacency W m z x = false ↔
        S.ρ x = i.val ∨ S.ρ x = p.val at hh
      cases hg : PhysicalRepresentative.adjacency W m z x with
      | false =>
        exact False.elim ((hh.mp hg).elim hx.1 hx.2)
      | true => rfl)
  · intro hx
    exact hp.mono (fun z hz hpz => (hz hpz).mpr hx)
  · intro hnot
    exact hp.mono (fun z hz hpz => by
      cases he : PhysicalRepresentative.adjacency W m z x with
      | false => rfl
      | true => exact False.elim (hnot ((hz hpz).mp he)))

private theorem ae_private_physical_vertex_data
    (S : SelectedHighLowStructure W m) (i p : S.I) (hip : i ≠ p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpeak : S.IsCommonForwardPeak d c i)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.H)
    (hprivate : ∀ᵐ q ∂μ.prod μ, S.ρ q.1 = i.val →
      adjacencyKernel W q.1 q.2 =
        if S.ρ q.2 = i.val ∨ S.ρ q.2 = p.val then 0 else 1)
    (hell : -m < 1) :
    ∀ᵐ x ∂μ,
      (∫ z, PhysicalRepresentative.charge W m z x +
        (-m) * (if PhysicalRepresentative.adjacency W m z x then 1 else 0) ∂μ) =
          2 * (c - m * d) ∧
      (S.ρ x = i.val → ∀ᵐ z ∂μ,
        PhysicalRepresentative.adjacency W m z x = false ↔
          S.ρ z = i.val ∨ S.ρ z = p.val) ∧
      (S.ρ x ≠ i.val ∧ S.ρ x ≠ p.val → ∀ᵐ z ∂μ,
        S.ρ z = i.val → PhysicalRepresentative.adjacency W m z x = true) ∧
      (x ∈ S.rootNeighborhood p → ∀ᵐ z ∂μ,
        S.ρ z = p.val → PhysicalRepresentative.adjacency W m z x = true) ∧
      (x ∉ S.rootNeighborhood p → ∀ᵐ z ∂μ,
        S.ρ z = p.val → PhysicalRepresentative.adjacency W m z x = false) ∧
      (x ∈ (({z | S.ρ z = i.val} ∪ {z | S.ρ z = p.val})ᶜ ∩
        S.rootNeighborhood p) →
        μ.real {z | PhysicalRepresentative.adjacency W m x z = false} ≤
          1 - 2 * μ.real {z | S.ρ z = i.val} -
            μ.real {z | S.ρ z = p.val}) ∧
      (x ∈ (({z | S.ρ z = i.val} ∪ {z | S.ρ z = p.val})ᶜ \
        S.rootNeighborhood p) → x ∉ S.D →
        μ.real {z | PhysicalRepresentative.adjacency W m x z = false} <
          μ.real {z | S.ρ z = i.val}) := by
  filter_upwards [S.ae_physical_shifted_column_stationary hW hd hgap,
    S.ae_private_physical_columns i p hW hd hgap hprivate,
    S.ae_private_neighbor_missing_capacity i p hip hW hd hgap hell hhigh hprivate,
    S.ae_private_hole_atomic_missing_lt_common_peak i p hip
      hW hd hgap hpeak hhigh hprivate] with x hmean hcolumns hN hK
  exact ⟨by
      convert hmean using 1
      congr 1
      funext z
      cases PhysicalRepresentative.adjacency W m z x <;> simp
      ring,
    hcolumns.1, hcolumns.2.1, hcolumns.2.2.1,
    hcolumns.2.2.2, hN, hK⟩

/-- A tight triangle of the same original selected model exposes every
private root star in the large private sector `3A + b > 1`. A leaf in the
second whole fiber's hole has the stronger signed lower bound. The two
triangle margins are explicit; the parent law may be singular. -/
theorem ae_permuted_private_triangle_exposure_sector
    (S : SelectedHighLowStructure W m) (i p : S.I) (hip : i ≠ p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpeak : S.IsCommonForwardPeak d c i)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.H)
    (hprivate : ∀ᵐ q ∂μ.prod μ, S.ρ q.1 = i.val →
      adjacencyKernel W q.1 q.2 =
        if S.ρ q.2 = i.val ∨ S.ρ q.2 = p.val then 0 else 1)
    (hsector : 1 < 3 * μ.real {x | S.ρ x = i.val} + μ.real {x | S.ρ x = p.val})
    (hell : -m ∈ Ioo (1 / 2 : ℝ) 1)
    (hmargin : 2 * (1 + m) * μ.real {x | S.ρ x = i.val} <
      3 * (2 * (c - m * d) + m))
    (hNNmargin : (1 + m) * (1 - μ.real {x | S.ρ x = i.val}) <
      3 * (2 * (c - m * d) + m))
    (τ : Measure (Fin 3 → Ω)) [IsFiniteMeasure τ]
    (hpairs : ∀ a b : Fin 3, a ≠ b →
      τ.map (fun v => (v a, v b)) ≪ μ.prod μ)
    (hclique : ∀ᵐ v ∂τ, PhysicalCliqueRepresentative.Clique
      (Function.uncurry (PhysicalRepresentative.adjacency W m)) v)
    (htight : ∀ᵐ v ∂τ, PhysicalPrimal.charge
      (Function.uncurry (PhysicalRepresentative.charge W m)) v = 1) :
    ∀ᵐ v ∂τ, ∀ e : Equiv.Perm (Fin 3), S.ρ (v (e 0)) = i.val →
      0 < S.rootChargeRow i (v (e 1)) ∧
      (v (e 1) ∈ (({x | S.ρ x = i.val} ∪
        {x | S.ρ x = p.val})ᶜ \ S.rootNeighborhood p) →
        1 + m < S.rootChargeRow i (v (e 1))) := by
  let G := Function.uncurry (PhysicalRepresentative.adjacency W m)
  let Y := Function.uncurry (PhysicalRepresentative.charge W m)
  let I := {x | S.ρ x = i.val}
  let P := {x | S.ρ x = p.val}
  let E := I ∪ P
  let V := Eᶜ
  let N := V ∩ S.rootNeighborhood p
  let K := V \ S.rootNeighborhood p
  have hI : MeasurableSet I := (S.hfibers i.val i.property).1
  have hP : MeasurableSet P := (S.hfibers p.val p.property).1
  have hE : MeasurableSet E := hI.union hP
  have hdis : Disjoint I P :=
    Set.disjoint_left.mpr (fun _ hx hy =>
      hip (Subtype.ext (hx.symm.trans hy)))
  have hEreal : μ.real E = μ.real I + μ.real P := by
    exact measureReal_union hdis hP
  have htest : ∀ n, 2 ≤ n → ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ),
      PhysicalCliqueRepresentative.Clique G v → PhysicalPrimal.charge Y v ≤ 1 := by
    intro n _
    filter_upwards [PhysicalRepresentative.full_feasible W hW.full m
      (hW.strict_gap_structure hd hgap).strict_support hW.deterministic n] with v hv hc
    change PhysicalPrimal.charge (Function.uncurry
      (PhysicalRepresentative.charge W m)) v ≤ 1
    rw [MultipartiteHeadPrice.physicalCharge_eq_tupleCharge]
    exact hv hc
  have hins := PhysicalTriangleExposure.ae_insertion_le_majorant_permutations G
    (PhysicalRepresentative.measurable_adjacency W m)
    (PhysicalRepresentative.adjacency_symm W m) Y
    (PhysicalRepresentative.measurable_charge W m)
    (PhysicalRepresentative.charge_symm W m) 3 (by norm_num)
    (fun q => PhysicalRepresentative.charge_bound W m q.1 q.2)
    (fun q => (PhysicalRepresentative.charge_mem_Icc W m q.1 q.2).2)
    (fun q => PhysicalRepresentative.charge_zero_of_nonedge W m q.1 q.2)
    htest (-m) τ hpairs hclique htight
  have hvertex := S.ae_private_physical_vertex_data i p hip hW hd hgap
    hpeak hhigh hprivate hell.2
  have hcoords := ae_all_coordinates_private (by norm_num : 2 ≤ 3)
    τ hpairs _ hvertex
  have hrootPairs := ae_all_pairs_private τ hpairs _
    (S.ae_root_adjacency i hW hd hgap)
  have hchargePairs := ae_all_pairs_private τ hpairs _
    (S.ae_root_charge i hW hd hgap)
  have hVevent := ae_all_coordinates_private (by norm_num : 2 ≤ 3)
    τ hpairs _ (S.ae_private_rootNeighborhood_iff i p hW hd hgap hprivate)
  have hdiff := S.ae_permuted_diffuse_triangle_star_le hW hd hgap
    τ hpairs hclique htight
  filter_upwards [hins, hcoords, hrootPairs, hchargePairs, hVevent, hdiff,
    hclique, htight] with v hi hc hr hY hV hdif hv ht e hv0
  have he01 : e 0 ≠ e 1 :=
    fun h => (by decide : (0 : Fin 3) ≠ 1) (e.injective h)
  have he02 : e 0 ≠ e 2 :=
    fun h => (by decide : (0 : Fin 3) ≠ 2) (e.injective h)
  have hv1 : v (e 1) ∈ V := by
    have hn := (hr (e 0) (e 1) he01 hv0).mp (hv _ _ he01)
    simpa [V, E, I, P, not_or] using (hV (e 1)).mp hn
  have hv2 : v (e 2) ∈ V := by
    have hn := (hr (e 0) (e 2) he02 hv0).mp (hv _ _ he02)
    simpa [V, E, I, P, not_or] using (hV (e 2)).mp hn
  have hv1' : S.ρ (v (e 1)) ≠ i.val ∧ S.ρ (v (e 1)) ≠ p.val := by
    simpa [V, E, I, P, not_or] using hv1
  have hv2' : S.ρ (v (e 2)) ≠ i.val ∧ S.ρ (v (e 2)) ≠ p.val := by
    simpa [V, E, I, P, not_or] using hv2
  have hold : Y (v (e 0), v (e 1)) +
      Y (v (e 0), v (e 2)) + Y (v (e 1), v (e 2)) = 1 := by
    have ht' := (PhysicalTriangleExposure.charge_comp_equiv Y v e).trans ht
    have he : (fun j => v (e j)) = ![v (e 0), v (e 1), v (e 2)] := by
      funext j
      fin_cases j <;> rfl
    rw [he, PhysicalTriangleExposure.charge_three Y
      (PhysicalRepresentative.charge_symm W m)] at ht'
    exact ht'
  have hmean (j : Fin 3) :
      (∫ z, Y (z, v (e j)) +
        (-m) * (if G (z, v (e j)) then 1 else 0) ∂μ) =
          2 * (c - m * d) := (hc (e j)).1
  have hstar1D : v (e 1) ∈ S.D →
      Y (v (e 0), v (e 1)) + Y (v (e 1), v (e 2)) ≤ -m := by
    intro hD
    have hh := hdif ((Equiv.swap 0 1).trans e) hD
    change Y (v (e 1), v (e 0)) + Y (v (e 1), v (e 2)) ≤ -m at hh
    rw [show Y (v (e 1), v (e 0)) = Y (v (e 0), v (e 1)) from
      PhysicalRepresentative.charge_symm W m _ _] at hh
    exact hh
  have hstar2D : v (e 2) ∈ S.D →
      Y (v (e 0), v (e 2)) + Y (v (e 1), v (e 2)) ≤ -m := by
    intro hD
    have hh := hdif ((Equiv.swap 0 2).trans e) hD
    change Y (v (e 2), v (e 1)) + Y (v (e 2), v (e 0)) ≤ -m at hh
    rw [show Y (v (e 2), v (e 1)) = Y (v (e 1), v (e 2)) from
      PhysicalRepresentative.charge_symm W m _ _,
      show Y (v (e 2), v (e 0)) = Y (v (e 0), v (e 2)) from
      PhysicalRepresentative.charge_symm W m _ _] at hh
    linarith
  have hFsym (j : Fin 3) :
      μ.real {z | G (z, v (e j)) = false} =
        μ.real {z | PhysicalRepresentative.adjacency W m (v (e j)) z = false} := by
    congr 1
    ext z
    change (PhysicalRepresentative.adjacency W m z (v (e j)) = false) ↔
      (PhysicalRepresentative.adjacency W m (v (e j)) z = false)
    rw [PhysicalRepresentative.adjacency_symm W m z (v (e j))]
  have hFcap (j : Fin 3) (hvj : v (e j) ∈ V) (hnotD : v (e j) ∉ S.D) :
      μ.real {z | G (z, v (e j)) = false} ≤ μ.real I := by
    rw [hFsym]
    by_cases hn : v (e j) ∈ S.rootNeighborhood p
    · have hh := (hc (e j)).2.2.2.2.2.1 ⟨hvj, hn⟩
      linarith [hsector]
    · exact le_of_lt ((hc (e j)).2.2.2.2.2.2 ⟨hvj, hn⟩ hnotD)
  have hcoef1 :
      μ.real {z | G (z, v (e 1)) = false} *
          max (1 + m - Y (v (e 0), v (e 2))) 0 ≤
        μ.real I * max (1 + m - Y (v (e 0), v (e 2))) 0 := by
    by_cases hD : v (e 1) ∈ S.D
    · have hz : max (1 + m - Y (v (e 0), v (e 2))) 0 = 0 :=
        max_eq_right (by linarith [hold, hstar1D hD])
      simp only [hz, mul_zero, le_refl]
    · exact mul_le_mul_of_nonneg_right (hFcap 1 hv1 hD)
        (le_max_right _ _)
  have hcoef2 (hu : Y (v (e 0), v (e 1)) ≤ 1 + m) :
      μ.real {z | G (z, v (e 2)) = false} *
          (1 + m - Y (v (e 0), v (e 1))) ≤
        μ.real I * (1 + m - Y (v (e 0), v (e 1))) := by
    by_cases hD : v (e 2) ∈ S.D
    · have hz : 1 + m - Y (v (e 0), v (e 1)) = 0 := by
        linarith [hold, hstar2D hD]
      simp only [hz, mul_zero, le_refl]
    · exact mul_le_mul_of_nonneg_right (hFcap 2 hv2 hD) (by linarith)
  have hNN : v (e 1) ∈ N → v (e 2) ∈ N →
      0 < Y (v (e 0), v (e 1)) := by
    intro hN1 hN2
    by_contra hu
    have hu' : Y (v (e 0), v (e 1)) ≤ 0 := le_of_not_gt hu
    have hs1 : Y (v (e 0), v (e 1)) + Y (v (e 1), v (e 2)) =
        1 - Y (v (e 0), v (e 2)) := by linarith [hold]
    have hs2 : Y (v (e 0), v (e 2)) + Y (v (e 1), v (e 2)) =
        1 - Y (v (e 0), v (e 1)) := by linarith [hold]
    have hcover : ∀ᵐ z ∂μ,
        TriangleInsertion.majorant (-m)
          (Y (v (e 0), v (e 1)) + Y (v (e 0), v (e 2)))
          (Y (v (e 0), v (e 1)) + Y (v (e 1), v (e 2)))
          (Y (v (e 0), v (e 2)) + Y (v (e 1), v (e 2)))
          (G (z, v (e 0))) (G (z, v (e 1))) (G (z, v (e 2))) ≤
          E.indicator (fun _ => Y (v (e 0), v (e 1)) +
            Y (v (e 0), v (e 2)) + m) z +
          {z | G (z, v (e 1)) = false}.indicator
            (fun _ => max (1 + m - Y (v (e 0), v (e 2))) 0) z +
          {z | G (z, v (e 2)) = false}.indicator
            (fun _ => 1 + m - Y (v (e 0), v (e 1))) z := by
      filter_upwards [(hc (e 0)).2.1 hv0,
        (hc (e 1)).2.2.1 hv1', (hc (e 2)).2.2.1 hv2',
        (hc (e 1)).2.2.2.1 hN1.2,
        (hc (e 2)).2.2.2.1 hN2.2] with z hroot hI1 hI2 hP1 hP2
      have hr : G (z, v (e 0)) = false ↔ z ∈ E := by
        simpa [G, E, I, P] using hroot
      have hleaf1 : z ∈ E → G (z, v (e 1)) = true := by
        rintro (hzI | hzP)
        · exact hI1 hzI
        · exact hP1 hzP
      have hleaf2 : z ∈ E → G (z, v (e 2)) = true := by
        rintro (hzI | hzP)
        · exact hI2 hzI
        · exact hP2 hzP
      have hh := TriangleInsertion.majorant_le_universal_cover (-m)
        (Y (v (e 0), v (e 1))) (Y (v (e 0), v (e 2)))
        (G (z, v (e 0))) (G (z, v (e 1))) (G (z, v (e 2)))
        (z ∈ E) hr hleaf1 hleaf2 (by linarith [hell.1]) hu'
      simpa only [hs1, hs2, Set.indicator, mem_ofPred_eq,
        sub_neg_eq_add] using hh
    have hint := triangle_integral_le_private_cover G
      (PhysicalRepresentative.measurable_adjacency W m) Y
      (PhysicalRepresentative.measurable_charge W m) 3
      (fun q => PhysicalRepresentative.charge_bound W m q.1 q.2)
      (-m) (2 * (c - m * d)) (fun j => v (e j)) E hE hmean
      (hi e) (by simpa only [sub_neg_eq_add] using hcover)
    have hF1 := (hc (e 1)).2.2.2.2.2.1 hN1
    have hF2 := (hc (e 2)).2.2.2.2.2.1 hN2
    have hF1' : μ.real {z | G (z, v (e 1)) = false} ≤
        1 - 2 * μ.real I - μ.real P := by
      convert hF1 using 1
      congr 1
      ext z
      change (PhysicalRepresentative.adjacency W m z (v (e 1)) = false) ↔
        (PhysicalRepresentative.adjacency W m (v (e 1)) z = false)
      rw [PhysicalRepresentative.adjacency_symm W m z (v (e 1))]
    have hF2' : μ.real {z | G (z, v (e 2)) = false} ≤
        1 - 2 * μ.real I - μ.real P := by
      convert hF2 using 1
      congr 1
      ext z
      change (PhysicalRepresentative.adjacency W m z (v (e 2)) = false) ↔
        (PhysicalRepresentative.adjacency W m (v (e 2)) z = false)
      rw [PhysicalRepresentative.adjacency_symm W m z (v (e 2))]
    have hv' := (PhysicalRepresentative.charge_mem_Icc W m
      (v (e 0)) (v (e 2))).2
    have hb : 0 ≤ μ.real P := measureReal_nonneg
    have hh := private_NN_root_charge_pos (μ.real I) (μ.real P) (-m)
      (2 * (c - m * d)) (Y (v (e 0), v (e 1)))
      (Y (v (e 0), v (e 2)))
      (μ.real {z | G (z, v (e 1)) = false})
      (μ.real {z | G (z, v (e 2)) = false})
      hb hsector hell
      (by simpa only [sub_neg_eq_add] using hNNmargin)
      hv' hF1' hF2' (by
        rw [hEreal] at hint
        simpa only [sub_neg_eq_add] using hint)
    exact hu hh
  have hKfirst : v (e 1) ∈ K →
      1 + m < Y (v (e 0), v (e 1)) := by
    intro hK1
    by_contra hu
    have hu' : Y (v (e 0), v (e 1)) ≤ 1 + m := le_of_not_gt hu
    have hs1 : Y (v (e 0), v (e 1)) + Y (v (e 1), v (e 2)) =
        1 - Y (v (e 0), v (e 2)) := by linarith [hold]
    have hs2 : Y (v (e 0), v (e 2)) + Y (v (e 1), v (e 2)) =
        1 - Y (v (e 0), v (e 1)) := by linarith [hold]
    have hcover : ∀ᵐ z ∂μ,
        TriangleInsertion.majorant (-m)
          (Y (v (e 0), v (e 1)) + Y (v (e 0), v (e 2)))
          (Y (v (e 0), v (e 1)) + Y (v (e 1), v (e 2)))
          (Y (v (e 0), v (e 2)) + Y (v (e 1), v (e 2)))
          (G (z, v (e 0))) (G (z, v (e 1))) (G (z, v (e 2))) ≤
          I.indicator (fun _ => Y (v (e 0), v (e 1)) +
            Y (v (e 0), v (e 2)) + m) z +
          {z | G (z, v (e 1)) = false}.indicator
            (fun _ => max (1 + m - Y (v (e 0), v (e 2))) 0) z +
          {z | G (z, v (e 2)) = false}.indicator
            (fun _ => 1 + m - Y (v (e 0), v (e 1))) z := by
      filter_upwards [(hc (e 0)).2.1 hv0,
        (hc (e 1)).2.2.1 hv1', (hc (e 2)).2.2.1 hv2',
        (hc (e 1)).2.2.2.2.1 hK1.2] with z hroot hI1 hI2 hP1
      have hr : G (z, v (e 0)) = false ↔ z ∈ I ∨ z ∈ P := by
        simpa [G, I, P] using hroot
      have hh := TriangleInsertion.majorant_le_private_K_cover (-m)
        (Y (v (e 0), v (e 1))) (Y (v (e 0), v (e 2)))
        (G (z, v (e 0))) (G (z, v (e 1))) (G (z, v (e 2)))
        (z ∈ I) (z ∈ P) hr hI1 hI2 hP1
        (by linarith [hell.1])
        (by simpa only [sub_neg_eq_add] using hu')
      simpa only [hs1, hs2, Set.indicator, mem_ofPred_eq,
        sub_neg_eq_add] using hh
    have hint := triangle_integral_le_private_cover G
      (PhysicalRepresentative.measurable_adjacency W m) Y
      (PhysicalRepresentative.measurable_charge W m) 3
      (fun q => PhysicalRepresentative.charge_bound W m q.1 q.2)
      (-m) (2 * (c - m * d)) (fun j => v (e j)) I hI hmean
      (hi e) (by simpa only [sub_neg_eq_add] using hcover)
    have hv' := (PhysicalRepresentative.charge_mem_Icc W m
      (v (e 0)) (v (e 2))).2
    have hh := private_K_root_charge_gt (μ.real I) (-m)
      (2 * (c - m * d)) (Y (v (e 0), v (e 1)))
      (Y (v (e 0), v (e 2)))
      (μ.real {z | G (z, v (e 1)) = false})
      (μ.real {z | G (z, v (e 2)) = false})
      (measureReal_nonneg) (by linarith [hell.1])
      (by simpa only [sub_neg_eq_add] using hmargin)
      hv' (by simpa only [sub_neg_eq_add] using hcoef1)
      (by simpa only [sub_neg_eq_add] using hcoef2 hu')
      (by simpa only [sub_neg_eq_add] using hint)
    exact hu (by simpa only [sub_neg_eq_add] using hh)
  have hKsecond : v (e 2) ∈ K →
      0 < Y (v (e 0), v (e 1)) := by
    intro hK2
    by_contra hu
    have hu' : Y (v (e 0), v (e 1)) ≤ 0 := le_of_not_gt hu
    have huδ : Y (v (e 0), v (e 1)) ≤ 1 + m := by
      linarith [hell.2]
    have hs1 : Y (v (e 0), v (e 1)) + Y (v (e 1), v (e 2)) =
        1 - Y (v (e 0), v (e 2)) := by linarith [hold]
    have hs2 : Y (v (e 0), v (e 2)) + Y (v (e 1), v (e 2)) =
        1 - Y (v (e 0), v (e 1)) := by linarith [hold]
    have hcover : ∀ᵐ z ∂μ,
        TriangleInsertion.majorant (-m)
          (Y (v (e 0), v (e 1)) + Y (v (e 0), v (e 2)))
          (Y (v (e 0), v (e 1)) + Y (v (e 1), v (e 2)))
          (Y (v (e 0), v (e 2)) + Y (v (e 1), v (e 2)))
          (G (z, v (e 0))) (G (z, v (e 1))) (G (z, v (e 2))) ≤
          I.indicator (fun _ => Y (v (e 0), v (e 1)) +
            Y (v (e 0), v (e 2)) + m) z +
          {z | G (z, v (e 1)) = false}.indicator
            (fun _ => max (1 + m - Y (v (e 0), v (e 2))) 0) z +
          {z | G (z, v (e 2)) = false}.indicator
            (fun _ => 1 + m - Y (v (e 0), v (e 1))) z := by
      filter_upwards [(hc (e 0)).2.1 hv0,
        (hc (e 1)).2.2.1 hv1', (hc (e 2)).2.2.1 hv2',
        (hc (e 2)).2.2.2.2.1 hK2.2] with z hroot hI1 hI2 hP2
      have hr : G (z, v (e 0)) = false ↔ z ∈ I ∨ z ∈ P := by
        simpa [G, I, P] using hroot
      have hh := majorant_le_private_second_K_cover (-m)
        (Y (v (e 0), v (e 1))) (Y (v (e 0), v (e 2)))
        (G (z, v (e 0))) (G (z, v (e 1))) (G (z, v (e 2)))
        (z ∈ I) (z ∈ P) hr hI1 hI2 hP2
        (by linarith [hell.1]) hu'
      simpa only [hs1, hs2, Set.indicator, mem_ofPred_eq,
        sub_neg_eq_add] using hh
    have hint := triangle_integral_le_private_cover G
      (PhysicalRepresentative.measurable_adjacency W m) Y
      (PhysicalRepresentative.measurable_charge W m) 3
      (fun q => PhysicalRepresentative.charge_bound W m q.1 q.2)
      (-m) (2 * (c - m * d)) (fun j => v (e j)) I hI hmean
      (hi e) (by simpa only [sub_neg_eq_add] using hcover)
    have hv' := (PhysicalRepresentative.charge_mem_Icc W m
      (v (e 0)) (v (e 2))).2
    have hh := private_K_root_charge_gt (μ.real I) (-m)
      (2 * (c - m * d)) (Y (v (e 0), v (e 1)))
      (Y (v (e 0), v (e 2)))
      (μ.real {z | G (z, v (e 1)) = false})
      (μ.real {z | G (z, v (e 2)) = false})
      (measureReal_nonneg) (by linarith [hell.1])
      (by simpa only [sub_neg_eq_add] using hmargin)
      hv' (by simpa only [sub_neg_eq_add] using hcoef1)
      (by simpa only [sub_neg_eq_add] using hcoef2 huδ)
      (by simpa only [sub_neg_eq_add] using hint)
    exact (not_lt_of_ge hu') (lt_of_le_of_lt (by linarith [hell.2]) hh)
  have hrow : Y (v (e 0), v (e 1)) = S.rootChargeRow i (v (e 1)) :=
    hY (e 0) (e 1) he01 hv0
  have hpositive : 0 < Y (v (e 0), v (e 1)) := by
    by_cases hk1 : v (e 1) ∈ K
    · exact lt_trans (by linarith [hell.2]) (hKfirst hk1)
    have hn1 : v (e 1) ∈ N := by
      refine ⟨hv1, ?_⟩
      by_contra hnot
      exact hk1 ⟨hv1, hnot⟩
    by_cases hk2 : v (e 2) ∈ K
    · exact hKsecond hk2
    have hn2 : v (e 2) ∈ N := by
      refine ⟨hv2, ?_⟩
      by_contra hnot
      exact hk2 ⟨hv2, hnot⟩
    exact hNN hn1 hn2
  rw [← hrow]
  refine ⟨hpositive, ?_⟩
  intro hk
  exact hKfirst hk

end Erdos1017.CappedModel.SelectedHighLowStructure
