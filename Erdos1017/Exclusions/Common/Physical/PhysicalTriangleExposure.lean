module

public import Erdos1017.Exclusions.Common.TriangleInsertion
public import Erdos1017.Exclusions.Common.MultipartiteHeadPrice
public import Erdos1017.SelectedModel.PhysicalPrimal.PhysicalCliqueRepresentative

/-!
# Fresh-point insertion into tight triangles

Independently resampling one point gives the fresh-point triangle insertion
inequality at almost every tight triangle parent, in every coordinate order, and
integrating it against flat shifted rows forces the first universal-root star
positive.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators

namespace Erdos1017.PhysicalTriangleExposure

private theorem clique_cons {Ω : Type*} (G : Ω × Ω → Bool)
    (hsym : ∀ x y, G (x, y) = G (y, x)) {n : ℕ} (v : Fin n → Ω)
    (hv : PhysicalCliqueRepresentative.Clique G v) (z : Ω)
    (hz : ∀ i, G (z, v i) = true) :
    PhysicalCliqueRepresentative.Clique G (Fin.cons z v) := by
  intro i j hij
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => exact (hij rfl).elim
    | succ j => exact hz j
  | succ i =>
    cases j using Fin.cases with
    | zero => simpa only [Fin.cons_succ, Fin.cons_zero, hsym] using hz i
    | succ j => exact hv i j (fun h => hij (congrArg Fin.succ h))

private theorem clique_two {Ω : Type*} (G : Ω × Ω → Bool)
    (hsym : ∀ x y, G (x, y) = G (y, x)) (x y : Ω) (hxy : G (x, y) = true) :
    PhysicalCliqueRepresentative.Clique G ![x, y] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [hsym y x]

private theorem charge_eq_tupleCharge {Ω : Type*} (Y : Ω × Ω → ℝ)
    {n : ℕ} (v : Fin n → Ω) :
    PhysicalPrimal.charge Y v = FiniteArity.tupleCharge (fun x y => Y (x, y)) v := by
  have he : Function.uncurry (fun x y => Y (x, y)) = Y := by
    funext p
    cases p
    rfl
  simpa only [he] using MultipartiteHeadPrice.physicalCharge_eq_tupleCharge
    (fun x y => Y (x, y)) v

/-- Adding one physical point adds its entire old-vertex star to the
original ordered-pair charge, at every finite order. -/
theorem charge_cons {Ω : Type*} (Y : Ω × Ω → ℝ)
    (hsym : ∀ x y, Y (x, y) = Y (y, x)) {n : ℕ} (v : Fin n → Ω) (z : Ω) :
    PhysicalPrimal.charge Y (Fin.cons z v) =
      (∑ i, Y (z, v i)) + PhysicalPrimal.charge Y v := by
  rw [charge_eq_tupleCharge,
    FiniteArity.tupleCharge_cons (fun x y => Y (x, y)) z v
      (fun i => (hsym z (v i)).symm), ← charge_eq_tupleCharge]

/-- Relabeling the coordinates preserves the actual ordered-pair charge. -/
theorem charge_comp_equiv {Ω : Type*} (Y : Ω × Ω → ℝ) {n : ℕ}
    (v : Fin n → Ω) (e : Equiv.Perm (Fin n)) :
    PhysicalPrimal.charge Y (fun i => v (e i)) = PhysicalPrimal.charge Y v := by
  rw [charge_eq_tupleCharge, charge_eq_tupleCharge]
  change FiniteArity.tupleCharge (fun x y => Y (x, y))
    (fun i => v (e.toEmbedding i)) = _
  rw [FiniteArity.tupleCharge_subtuple (fun x y => Y (x, y)) v e.toEmbedding,
    Finset.map_univ_equiv]
  rfl

theorem charge_three {Ω : Type*} (Y : Ω × Ω → ℝ)
    (hsym : ∀ x y, Y (x, y) = Y (y, x)) (x y z : Ω) :
    PhysicalPrimal.charge Y ![x, y, z] = Y (x, y) + Y (x, z) + Y (y, z) := by
  rw [charge_eq_tupleCharge Y]
  simp [FiniteArity.tupleCharge, FiniteArity.pairCharge, FiniteArity.crossSum,
    Fin.sum_univ_succ, hsym y x, hsym z x, hsym z y]
  ring

private theorem charge_cons_three {Ω : Type*} (Y : Ω × Ω → ℝ)
    (hsym : ∀ x y, Y (x, y) = Y (y, x)) (v : Fin 3 → Ω) (z : Ω) :
    PhysicalPrimal.charge Y (Fin.cons z v) = PhysicalPrimal.charge Y v +
      (Y (z, v 0) + Y (z, v 1) + Y (z, v 2)) := by
  rw [charge_cons Y hsym, Fin.sum_univ_three]
  ring

variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace.CountablyGenerated Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Genuine original finite-clique tests, licensed at regular physical
pairs, give the fresh-point triangle insertion inequality. The regular
pairs will be derived under independently enlarged singular parent laws. -/
theorem insertion_le_majorant_of_pairRegular
    (G : Ω × Ω → Bool) (hG : Measurable G)
    (hGsym : ∀ x y, G (x, y) = G (y, x))
    (Y : Ω × Ω → ℝ) (hY : Measurable Y)
    (hYsym : ∀ x y, Y (x, y) = Y (y, x))
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ p, |Y p| ≤ B)
    (hcap : ∀ p, Y p ≤ 1) (hzero : ∀ p, G p = false → Y p = 0)
    (htest : ∀ n, 2 ≤ n → ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ),
      PhysicalCliqueRepresentative.Clique G v → PhysicalPrimal.charge Y v ≤ 1)
    (ell : ℝ) (v : Fin 3 → Ω) (z : Ω)
    (hv : PhysicalCliqueRepresentative.Clique G v) (htight : PhysicalPrimal.charge Y v = 1)
    (hregular : ∀ i j : Fin 4, i ≠ j →
      PhysicalCliqueRepresentative.PairRegular μ G Y
        ((Fin.cons z v : Fin 4 → Ω) i, (Fin.cons z v : Fin 4 → Ω) j)) :
    Y (z, v 0) + Y (z, v 1) + Y (z, v 2) -
      ell * ((if G (z, v 0) then 0 else 1) + (if G (z, v 1) then 0 else 1) +
        (if G (z, v 2) then 0 else 1)) ≤
      TriangleInsertion.majorant ell (Y (v 0, v 1) + Y (v 0, v 2))
        (Y (v 0, v 1) + Y (v 1, v 2)) (Y (v 0, v 2) + Y (v 1, v 2))
        (G (z, v 0)) (G (z, v 1)) (G (z, v 2)) := by
  have hold : Y (v 0, v 1) + Y (v 0, v 2) + Y (v 1, v 2) = 1 := by
    have he : v = ![v 0, v 1, v 2] := by ext i; fin_cases i <;> rfl
    rw [he, charge_three Y hYsym] at htight
    exact htight
  have hsub (e : Fin 3 ↪ Fin 4)
      (hc : PhysicalCliqueRepresentative.Clique G (fun i => (Fin.cons z v : Fin 4 → Ω) (e i))) :
      PhysicalPrimal.charge Y (fun i => (Fin.cons z v : Fin 4 → Ω) (e i)) ≤ 1 :=
    PhysicalCliqueRepresentative.charge_le_of_pairRegular μ hG hY B hB hbound htest 3 (fun i => (Fin.cons z v : Fin 4 → Ω) (e i)) hc
      (fun i j hij => hregular (e i) (e j) (fun h => hij (e.injective h)))
  apply TriangleInsertion.insertion_le_majorant
  · exact hzero _
  · exact hzero _
  · exact hzero _
  · intro _; exact hcap _
  · intro _; exact hcap _
  · intro _; exact hcap _
  · intro hz0 hz1
    let e : Fin 3 ↪ Fin 4 := ⟨![0, 1, 2], by decide⟩
    have hc : PhysicalCliqueRepresentative.Clique G ![z, v 0, v 1] :=
      clique_cons G hGsym ![v 0, v 1] (clique_two G hGsym _ _ (hv 0 1 (by decide))) z
        (fun i => by fin_cases i <;> assumption)
    have heq : (fun i => (Fin.cons z v : Fin 4 → Ω) (e i)) = ![z, v 0, v 1] := by
      funext i
      fin_cases i <;> rfl
    have hh := hsub e (heq.symm ▸ hc)
    rw [heq, charge_three Y hYsym] at hh
    linarith
  · intro hz0 hz2
    let e : Fin 3 ↪ Fin 4 := ⟨![0, 1, 3], by decide⟩
    have hc : PhysicalCliqueRepresentative.Clique G ![z, v 0, v 2] :=
      clique_cons G hGsym ![v 0, v 2] (clique_two G hGsym _ _ (hv 0 2 (by decide))) z
        (fun i => by fin_cases i <;> assumption)
    have heq : (fun i => (Fin.cons z v : Fin 4 → Ω) (e i)) = ![z, v 0, v 2] := by
      funext i
      fin_cases i <;> rfl
    have hh := hsub e (heq.symm ▸ hc)
    rw [heq, charge_three Y hYsym] at hh
    linarith
  · intro hz1 hz2
    let e : Fin 3 ↪ Fin 4 := ⟨![0, 2, 3], by decide⟩
    have hc : PhysicalCliqueRepresentative.Clique G ![z, v 1, v 2] :=
      clique_cons G hGsym ![v 1, v 2] (clique_two G hGsym _ _ (hv 1 2 (by decide))) z
        (fun i => by fin_cases i <;> assumption)
    have heq : (fun i => (Fin.cons z v : Fin 4 → Ω) (e i)) = ![z, v 1, v 2] := by
      funext i
      fin_cases i <;> rfl
    have hh := hsub e (heq.symm ▸ hc)
    rw [heq, charge_three Y hYsym] at hh
    linarith
  · intro hz0 hz1 hz2
    have hc := clique_cons G hGsym v hv z (fun i => by fin_cases i <;> assumption)
    have hh := PhysicalCliqueRepresentative.charge_le_of_pairRegular μ hG hY B hB hbound
      htest 4 (Fin.cons z v) hc hregular
    rw [charge_cons_three Y hYsym, htight] at hh
    linarith

/-- One common physical event licenses every coordinate order of the old
triangle, with the fresh original sample independent in each application. -/
theorem ae_insertion_le_majorant_permutations
    (G : Ω × Ω → Bool) (hG : Measurable G)
    (hGsym : ∀ x y, G (x, y) = G (y, x))
    (Y : Ω × Ω → ℝ) (hY : Measurable Y)
    (hYsym : ∀ x y, Y (x, y) = Y (y, x))
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ p, |Y p| ≤ B)
    (hcap : ∀ p, Y p ≤ 1) (hzero : ∀ p, G p = false → Y p = 0)
    (htest : ∀ n, 2 ≤ n → ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ),
      PhysicalCliqueRepresentative.Clique G v → PhysicalPrimal.charge Y v ≤ 1)
    (ell : ℝ) (ρ : Measure (Fin 3 → Ω)) [IsFiniteMeasure ρ]
    (hpairs : ∀ i j : Fin 3, i ≠ j → ρ.map (fun v => (v i, v j)) ≪ μ.prod μ)
    (hclique : ∀ᵐ v ∂ρ, PhysicalCliqueRepresentative.Clique G v)
    (htight : ∀ᵐ v ∂ρ, PhysicalPrimal.charge Y v = 1) :
    ∀ᵐ v ∂ρ, ∀ e : Equiv.Perm (Fin 3), ∀ᵐ z ∂μ,
      Y (z, v (e 0)) + Y (z, v (e 1)) + Y (z, v (e 2)) -
        ell * ((if G (z, v (e 0)) then 0 else 1) + (if G (z, v (e 1)) then 0 else 1) +
          (if G (z, v (e 2)) then 0 else 1)) ≤
        TriangleInsertion.majorant ell (Y (v (e 0), v (e 1)) + Y (v (e 0), v (e 2)))
          (Y (v (e 0), v (e 1)) + Y (v (e 1), v (e 2))) (Y (v (e 0), v (e 2)) + Y (v (e 1), v (e 2)))
          (G (z, v (e 0))) (G (z, v (e 1))) (G (z, v (e 2))) := by
  have hreg := PhysicalCliqueRepresentative.ae_pairRegular μ hG hY B hbound
  have hfp := PhysicalCliqueRepresentative.freshLaw_pairs_absolutelyContinuous μ
    (by norm_num : 2 ≤ 3) ρ hpairs μ (Measure.absolutelyContinuous_refl μ)
  have hgood : ∀ᵐ w ∂PhysicalCliqueRepresentative.freshLaw μ ρ,
      ∀ i j : Fin 4, i ≠ j → PhysicalCliqueRepresentative.PairRegular μ G Y (w i, w j) := by
    simp only [ae_all_iff]
    intro i j hij
    exact ae_of_ae_map ((measurable_pi_apply i).prodMk
      (measurable_pi_apply j)).aemeasurable ((hfp i j hij).ae_le hreg)
  have hprod : ∀ᵐ p ∂μ.prod ρ, ∀ i j : Fin 4, i ≠ j →
      PhysicalCliqueRepresentative.PairRegular μ G Y
        ((Fin.cons p.1 p.2 : Fin 4 → Ω) i, (Fin.cons p.1 p.2 : Fin 4 → Ω) j) :=
    ae_of_ae_map PhysicalCliqueRepresentative.measurable_cons.aemeasurable hgood
  have hswap := (Measure.measurePreserving_swap (μ := ρ) (ν := μ)).quasiMeasurePreserving.ae hprod
  filter_upwards [hclique, htight, Measure.ae_ae_of_ae_prod hswap] with v hv ht hr e
  filter_upwards [hr] with z hz
  let E : Fin 4 → Fin 4 := Fin.cases 0 (fun i => (e i).succ)
  have hE : Function.Injective E := by
    intro i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => rfl
      | succ j => exact False.elim ((Fin.succ_ne_zero (e j)) hij.symm)
    | succ i =>
      cases j using Fin.cases with
      | zero => exact False.elim ((Fin.succ_ne_zero (e i)) hij)
      | succ j => exact congrArg Fin.succ (e.injective (Fin.succ_injective _ hij))
  have hpoint (i : Fin 4) :
      (Fin.cons z (fun j => v (e j)) : Fin 4 → Ω) i = (Fin.cons z v : Fin 4 → Ω) (E i) := by
    cases i using Fin.cases <;> rfl
  apply insertion_le_majorant_of_pairRegular G hG hGsym Y hY hYsym B hB hbound
    hcap hzero htest ell (fun i => v (e i)) z
  · intro i j hij
    exact hv (e i) (e j) (fun h => hij (e.injective h))
  · exact (charge_comp_equiv Y v e).trans ht
  · intro i j hij
    rw [hpoint i, hpoint j]
    exact hz (E i) (E j) (fun h => hij (hE h))

/-- Independently resampling one original point licenses the insertion
inequality at almost every actual tight triangle parent. Only the old
pair marginals are absolutely continuous; the parent law may be singular. -/
theorem ae_insertion_le_majorant
    (G : Ω × Ω → Bool) (hG : Measurable G)
    (hGsym : ∀ x y, G (x, y) = G (y, x))
    (Y : Ω × Ω → ℝ) (hY : Measurable Y)
    (hYsym : ∀ x y, Y (x, y) = Y (y, x))
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ p, |Y p| ≤ B)
    (hcap : ∀ p, Y p ≤ 1) (hzero : ∀ p, G p = false → Y p = 0)
    (htest : ∀ n, 2 ≤ n → ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ),
      PhysicalCliqueRepresentative.Clique G v → PhysicalPrimal.charge Y v ≤ 1)
    (ell : ℝ) (ρ : Measure (Fin 3 → Ω)) [IsFiniteMeasure ρ]
    (hpairs : ∀ i j : Fin 3, i ≠ j → ρ.map (fun v => (v i, v j)) ≪ μ.prod μ)
    (hclique : ∀ᵐ v ∂ρ, PhysicalCliqueRepresentative.Clique G v)
    (htight : ∀ᵐ v ∂ρ, PhysicalPrimal.charge Y v = 1) :
    ∀ᵐ v ∂ρ, ∀ᵐ z ∂μ,
      Y (z, v 0) + Y (z, v 1) + Y (z, v 2) -
        ell * ((if G (z, v 0) then 0 else 1) + (if G (z, v 1) then 0 else 1) +
          (if G (z, v 2) then 0 else 1)) ≤
        TriangleInsertion.majorant ell (Y (v 0, v 1) + Y (v 0, v 2))
          (Y (v 0, v 1) + Y (v 1, v 2)) (Y (v 0, v 2) + Y (v 1, v 2))
          (G (z, v 0)) (G (z, v 1)) (G (z, v 2)) := by
  have hreg := PhysicalCliqueRepresentative.ae_pairRegular μ hG hY B hbound
  have hfp := PhysicalCliqueRepresentative.freshLaw_pairs_absolutelyContinuous μ
    (by norm_num : 2 ≤ 3) ρ hpairs μ (Measure.absolutelyContinuous_refl μ)
  have hgood : ∀ᵐ w ∂PhysicalCliqueRepresentative.freshLaw μ ρ,
      ∀ i j : Fin 4, i ≠ j → PhysicalCliqueRepresentative.PairRegular μ G Y (w i, w j) := by
    simp only [ae_all_iff]
    intro i j hij
    exact ae_of_ae_map ((measurable_pi_apply i).prodMk
      (measurable_pi_apply j)).aemeasurable ((hfp i j hij).ae_le hreg)
  have hprod : ∀ᵐ p ∂μ.prod ρ, ∀ i j : Fin 4, i ≠ j →
      PhysicalCliqueRepresentative.PairRegular μ G Y
        ((Fin.cons p.1 p.2 : Fin 4 → Ω) i, (Fin.cons p.1 p.2 : Fin 4 → Ω) j) :=
    ae_of_ae_map PhysicalCliqueRepresentative.measurable_cons.aemeasurable hgood
  have hswap := (Measure.measurePreserving_swap (μ := ρ) (ν := μ)).quasiMeasurePreserving.ae hprod
  filter_upwards [hclique, htight, Measure.ae_ae_of_ae_prod hswap] with v hv ht hr
  filter_upwards [hr] with z hz
  exact insertion_le_majorant_of_pairRegular G hG hGsym Y hY hYsym B hB hbound
    hcap hzero htest ell v z hv ht hz


omit [MeasurableSpace.CountablyGenerated Ω] in
/-- Integrating the genuine insertion inequality against flat shifted
rows forces the first universal-root star positive. The signed root-region
term is retained exactly; only positive leaf coefficients use capacity. -/
theorem first_star_pos_of_insertion_and_capacity
    (G : Ω × Ω → Bool) (hG : Measurable G)
    (Y : Ω × Ω → ℝ) (hY : Measurable Y) (B : ℝ) (hbound : ∀ p, |Y p| ≤ B)
    (hcap : ∀ p, Y p ≤ 1) (ell ν : ℝ) (hell : ell ∈ Icc (1 / 2 : ℝ) 1)
    (v : Fin 3 → Ω) (I : Set Ω) (hI : MeasurableSet I)
    (hA : 1 / 3 ≤ μ.real I)
    (hmargin : (1 - ell) * (1 - μ.real I) < 3 * (ν - ell))
    (hold : Y (v 0, v 1) + Y (v 0, v 2) + Y (v 1, v 2) = 1)
    (hroot : ∀ᵐ z ∂μ, G (z, v 0) = false ↔ z ∈ I)
    (h1 : ∀ᵐ z ∂μ, z ∈ I → G (z, v 1) = true)
    (h2 : ∀ᵐ z ∂μ, z ∈ I → G (z, v 2) = true)
    (hmean : ∀ i : Fin 3, (∫ z, Y (z, v i) +
      ell * (if G (z, v i) then 1 else 0) ∂μ) = ν)
    (hmissing1 : μ.real {z | G (z, v 1) = false} ≤ 1 - 2 * μ.real I)
    (hmissing2 : μ.real {z | G (z, v 2) = false} ≤ 1 - 2 * μ.real I)
    (hinsertion : ∀ᵐ z ∂μ,
      Y (z, v 0) + Y (z, v 1) + Y (z, v 2) -
        ell * ((if G (z, v 0) then 0 else 1) + (if G (z, v 1) then 0 else 1) +
          (if G (z, v 2) then 0 else 1)) ≤
        TriangleInsertion.majorant ell (Y (v 0, v 1) + Y (v 0, v 2))
          (Y (v 0, v 1) + Y (v 1, v 2)) (Y (v 0, v 2) + Y (v 1, v 2))
          (G (z, v 0)) (G (z, v 1)) (G (z, v 2))) :
    0 < Y (v 0, v 1) := by
  classical
  by_contra hpos
  let u := Y (v 0, v 1)
  let w := Y (v 0, v 2)
  have hu : u ≤ 0 := le_of_not_gt hpos
  have hell0 : 0 ≤ ell := by linarith [hell.1]
  let F1 := {z | G (z, v 1) = false}
  let F2 := {z | G (z, v 2) = false}
  have hF1 : MeasurableSet F1 := (hG.comp (measurable_id.prodMk measurable_const))
    (measurableSet_singleton false)
  have hF2 : MeasurableSet F2 := (hG.comp (measurable_id.prodMk measurable_const))
    (measurableSet_singleton false)
  let L := fun z => Y (z, v 0) + Y (z, v 1) + Y (z, v 2) -
    ell * ((if G (z, v 0) then 0 else 1) + (if G (z, v 1) then 0 else 1) +
      (if G (z, v 2) then 0 else 1))
  let R := fun z => I.indicator (fun _ => u + w - ell) z +
    F1.indicator (fun _ => max (1 - ell - w) 0) z +
      F2.indicator (fun _ => 1 - ell - u) z
  have hle : L ≤ᵐ[μ] R := by
    filter_upwards [hinsertion, hroot, h1, h2] with z hi hr h1 h2
    have hs1 : Y (v 0, v 1) + Y (v 1, v 2) = 1 - w := by dsimp [w]; linarith
    have hs2 : Y (v 0, v 2) + Y (v 1, v 2) = 1 - u := by dsimp [u]; linarith
    rw [hs1, hs2] at hi
    have hm := TriangleInsertion.majorant_le_universal_cover ell u w
      (G (z, v 0)) (G (z, v 1)) (G (z, v 2)) (z ∈ I) hr h1 h2 hell0 hu
    have hh := hi.trans hm
    simpa only [L, R, u, w, F1, F2, Set.indicator, mem_ofPred_eq] using hh
  let f := fun i : Fin 3 => fun z => Y (z, v i) + ell * (if G (z, v i) then 1 else 0)
  have hf (i : Fin 3) : Integrable (f i) μ := by
    have hy : Integrable (fun z => Y (z, v i)) μ := Integrable.of_bound
      (hY.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable B
      (Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hbound (z, v i)))
    have hg : Integrable (fun z => if G (z, v i) then (1 : ℝ) else 0) μ :=
      Integrable.of_bound
        (Measurable.ite ((hG.comp (measurable_id.prodMk measurable_const))
          (measurableSet_singleton true)) measurable_const measurable_const).aestronglyMeasurable
        1 (Eventually.of_forall (fun z => by cases G (z, v i) <;> norm_num))
    exact hy.add (hg.const_mul ell)
  have hL : L = fun z => f 0 z + f 1 z + f 2 z - 3 * ell := by
    funext z
    cases h0 : G (z, v 0) <;> cases h1 : G (z, v 1) <;> cases h2 : G (z, v 2) <;>
      simp [L, f, h0, h1, h2] <;> ring
  have hiL : Integrable L μ := by
    rw [hL]
    exact (((hf 0).add (hf 1)).add (hf 2)).sub (integrable_const (3 * ell))
  have hmeanL : (∫ z, L z ∂μ) = 3 * (ν - ell) := by
    rw [hL, integral_sub, integral_add, integral_add]
    change (∫ z, f 0 z ∂μ) + (∫ z, f 1 z ∂μ) + (∫ z, f 2 z ∂μ) - _ = _
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
  have hi0 : Integrable (I.indicator (fun _ : Ω => u + w - ell)) μ :=
    (integrable_const _).indicator hI
  have hi1 : Integrable (F1.indicator (fun _ : Ω => max (1 - ell - w) 0)) μ :=
    (integrable_const _).indicator hF1
  have hi2 : Integrable (F2.indicator (fun _ : Ω => 1 - ell - u)) μ :=
    (integrable_const _).indicator hF2
  have hiR : Integrable R μ := (hi0.add hi1).add hi2
  have hmeanR : (∫ z, R z ∂μ) = μ.real I * (u + w - ell) +
      μ.real F1 * max (1 - ell - w) 0 + μ.real F2 * (1 - ell - u) := by
    rw [show R = fun z => I.indicator (fun _ => u + w - ell) z +
      F1.indicator (fun _ => max (1 - ell - w) 0) z +
      F2.indicator (fun _ => 1 - ell - u) z from rfl,
      integral_add, integral_add,
      integral_indicator hI, integral_indicator hF1, integral_indicator hF2]
    simp only [setIntegral_const, smul_eq_mul]
    all_goals first
      | exact hi0
      | exact hi1
      | exact hi2
      | exact hi0.add hi1
  have hh := integral_mono_ae hiL hiR hle
  rw [hmeanL, hmeanR] at hh
  have hm1 := mul_le_mul_of_nonneg_right hmissing1 (le_max_right (1 - ell - w) 0)
  have hm2 := mul_le_mul_of_nonneg_right hmissing2 (show 0 ≤ 1 - ell - u by linarith [hell.2])
  have hscalar := TriangleInsertion.nonpositive_star_capacity hA hell0 hu (hcap (v 0, v 2))
  change 3 * (ν - ell) ≤ μ.real I * (u + w - ell) +
    μ.real {z | G (z, v 1) = false} * max (1 - ell - w) 0 +
    μ.real {z | G (z, v 2) = false} * (1 - ell - u) at hh
  change μ.real I * (u + w - ell) + (1 - 2 * μ.real I) *
    (max (1 - ell - w) 0 + (1 - ell - u)) ≤ (1 - ell) * (1 - μ.real I) at hscalar
  nlinarith

end Erdos1017.PhysicalTriangleExposure
