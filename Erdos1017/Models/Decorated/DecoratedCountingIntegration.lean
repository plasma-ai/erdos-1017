module

public import Graphon.CutDistance
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Integration over two selected coordinates of a vertex sample

Two distinct coordinates of an independent finite vertex sample have the latent
product law, Fubini holds for them (`integral_two_coordinates`), and replacing
one edge color moment in a bounded finite-vertex product costs at most the
cut-norm difference of the two scalar graphons.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Erdos1017.DecoratedCounting

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Identify the two selected vertex indices in their specified order. -/
def pairIndexEquiv {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    Fin 2 ≃ {i : Fin n // i = a ∨ i = b} :=
  Equiv.ofBijective
    (fun j : Fin 2 => if j = 0 then ⟨a, Or.inl rfl⟩ else ⟨b, Or.inr rfl⟩)
    (by
      constructor
      · intro j k hjk
        fin_cases j <;> fin_cases k <;> simp_all
      · rintro ⟨i, hi⟩
        rcases hi with rfl | rfl
        · exact ⟨0, by simp⟩
        · exact ⟨1, by simp⟩)

/-- The selected two-coordinate product is the ordinary ordered pair. -/
def pairCoordinates {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    ({i : Fin n // i = a ∨ i = b} → Ω) ≃ᵐ Ω × Ω :=
  (MeasurableEquiv.piCongrLeft (fun _ : {i : Fin n // i = a ∨ i = b} => Ω)
    (pairIndexEquiv a b hab)).symm.trans MeasurableEquiv.finTwoArrow

private theorem pairCoordinates_measurePreserving {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    MeasurePreserving (pairCoordinates (Ω := Ω) a b hab)
      (Measure.pi (fun _ : {i : Fin n // i = a ∨ i = b} => μ)) (μ.prod μ) := by
  apply (measurePreserving_finTwoArrow μ).comp
  exact (measurePreserving_piCongrLeft (fun _ : {i : Fin n // i = a ∨ i = b} => μ)
    (pairIndexEquiv a b hab)).symm

/-- Split a finite vertex sample into two selected coordinates and the rest. -/
def splitCoordinates {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    (Fin n → Ω) ≃ᵐ (Ω × Ω) × ({i : Fin n // ¬(i = a ∨ i = b)} → Ω) :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => Ω)
    (fun i => i = a ∨ i = b)).trans
      ((pairCoordinates (Ω := Ω) a b hab).prodCongr (MeasurableEquiv.refl _))

private theorem splitCoordinates_measurePreserving {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    MeasurePreserving (splitCoordinates (Ω := Ω) a b hab)
      (Measure.pi (fun _ : Fin n => μ))
      ((μ.prod μ).prod (Measure.pi (fun _ : {i : Fin n // ¬(i = a ∨ i = b)} => μ))) := by
  apply ((pairCoordinates_measurePreserving (μ := μ) a b hab).prod
    (MeasurePreserving.id _)).comp
  exact measurePreserving_piEquivPiSubtypeProd (fun _ : Fin n => μ)
    (fun i => i = a ∨ i = b)

private theorem splitCoordinates_apply_fst {n : ℕ} (a b : Fin n) (hab : a ≠ b)
    (z : Fin n → Ω) : (splitCoordinates a b hab z).1 = (z a, z b) := by
  change pairCoordinates a b hab (fun i => z i) = (z a, z b)
  have h0 : pairIndexEquiv a b hab 0 = ⟨a, Or.inl rfl⟩ := by
    apply Subtype.ext
    change (if (0 : Fin 2) = 0 then a else b) = a
    simp
  have h1 : pairIndexEquiv a b hab 1 = ⟨b, Or.inr rfl⟩ := by
    apply Subtype.ext
    change (if (1 : Fin 2) = 0 then a else b) = b
    simp
  simp [pairCoordinates, MeasurableEquiv.piCongrLeft,
    Equiv.piCongrLeft_symm_apply, h0, h1]

private theorem splitCoordinates_apply_snd {n : ℕ} (a b : Fin n) (hab : a ≠ b)
    (z : Fin n → Ω) : (splitCoordinates a b hab z).2 =
      fun i : {i : Fin n // ¬(i = a ∨ i = b)} => z i := rfl

private theorem splitCoordinates_symm_apply_a {n : ℕ} (a b : Fin n) (hab : a ≠ b)
    (p : Ω × Ω) (t : {i : Fin n // ¬(i = a ∨ i = b)} → Ω) :
    ((splitCoordinates a b hab).symm (p, t)) a = p.1 := by
  have h := splitCoordinates_apply_fst a b hab ((splitCoordinates a b hab).symm (p, t))
  rw [MeasurableEquiv.apply_symm_apply] at h
  exact (congrArg Prod.fst h).symm

private theorem splitCoordinates_symm_apply_b {n : ℕ} (a b : Fin n) (hab : a ≠ b)
    (p : Ω × Ω) (t : {i : Fin n // ¬(i = a ∨ i = b)} → Ω) :
    ((splitCoordinates a b hab).symm (p, t)) b = p.2 := by
  have h := splitCoordinates_apply_fst a b hab ((splitCoordinates a b hab).symm (p, t))
  rw [MeasurableEquiv.apply_symm_apply] at h
  exact (congrArg Prod.snd h).symm

private theorem splitCoordinates_symm_apply_other {n : ℕ} (a b : Fin n) (hab : a ≠ b)
    (p : Ω × Ω) (t : {i : Fin n // ¬(i = a ∨ i = b)} → Ω)
    (i : Fin n) (hi : ¬(i = a ∨ i = b)) :
    ((splitCoordinates a b hab).symm (p, t)) i = t ⟨i, hi⟩ := by
  have h := splitCoordinates_apply_snd a b hab ((splitCoordinates a b hab).symm (p, t))
  rw [MeasurableEquiv.apply_symm_apply] at h
  exact (congrFun h ⟨i, hi⟩).symm

/-- Two distinct coordinates of an independent finite vertex sample have
exactly the latent product law. -/
theorem measurePreserving_pairProjection {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    MeasurePreserving (fun z : Fin n → Ω => (z a, z b))
      (Measure.pi (fun _ : Fin n => μ)) (μ.prod μ) := by
  have h := (measurePreserving_fst (μ := μ.prod μ)
    (ν := Measure.pi (fun _ : {i : Fin n // ¬(i = a ∨ i = b)} => μ))).comp
      (splitCoordinates_measurePreserving (μ := μ) a b hab)
  convert h using 1
  funext z
  exact (splitCoordinates_apply_fst a b hab z).symm

private theorem splitCoordinates_symm_update_a {n : ℕ} (a b : Fin n) (hab : a ≠ b)
    (x x' y : Ω) (t : {i : Fin n // ¬(i = a ∨ i = b)} → Ω) :
    (splitCoordinates a b hab).symm ((x', y), t) =
      Function.update ((splitCoordinates a b hab).symm ((x, y), t)) a x' := by
  funext i
  by_cases hia : i = a
  · subst i
    simp [splitCoordinates_symm_apply_a]
  by_cases hib : i = b
  · subst i
    rw [Function.update_of_ne (Ne.symm hab), splitCoordinates_symm_apply_b,
      splitCoordinates_symm_apply_b]
  have hi : ¬(i = a ∨ i = b) := by simp [hia, hib]
  rw [Function.update_of_ne hia, splitCoordinates_symm_apply_other a b hab _ t i hi,
    splitCoordinates_symm_apply_other a b hab _ t i hi]

private theorem splitCoordinates_symm_update_b {n : ℕ} (a b : Fin n) (hab : a ≠ b)
    (x y y' : Ω) (t : {i : Fin n // ¬(i = a ∨ i = b)} → Ω) :
    (splitCoordinates a b hab).symm ((x, y'), t) =
      Function.update ((splitCoordinates a b hab).symm ((x, y), t)) b y' := by
  funext i
  by_cases hib : i = b
  · subst i
    simp [splitCoordinates_symm_apply_b]
  by_cases hia : i = a
  · subst i
    rw [Function.update_of_ne hab, splitCoordinates_symm_apply_a,
      splitCoordinates_symm_apply_a]
  have hi : ¬(i = a ∨ i = b) := by simp [hia, hib]
  rw [Function.update_of_ne hib, splitCoordinates_symm_apply_other a b hab _ t i hi,
    splitCoordinates_symm_apply_other a b hab _ t i hi]

/-- Fubini for two specified distinct coordinates of a finite product law. -/
theorem integral_two_coordinates {n : ℕ} (a b : Fin n) (hab : a ≠ b)
    (H : (Fin n → Ω) → ℝ) (hH : Integrable H (Measure.pi (fun _ : Fin n => μ))) :
    (∫ z, H z ∂Measure.pi (fun _ : Fin n => μ)) =
      ∫ t : {i : Fin n // ¬(i = a ∨ i = b)} → Ω,
        ∫ p : Ω × Ω, H ((splitCoordinates a b hab).symm (p, t)) ∂μ.prod μ
          ∂Measure.pi (fun _ => μ) := by
  let e := splitCoordinates (Ω := Ω) a b hab
  have he := (splitCoordinates_measurePreserving (μ := μ) a b hab).symm.integral_comp' H
  have hint : Integrable (fun q : (Ω × Ω) ×
      ({i : Fin n // ¬(i = a ∨ i = b)} → Ω) => H (e.symm q))
      ((μ.prod μ).prod (Measure.pi (fun _ => μ))) := by
    exact ((splitCoordinates_measurePreserving (μ := μ) a b hab).symm.integrable_comp_emb
      e.symm.measurableEmbedding).2 hH
  rw [integral_prod_symm _ hint] at he
  exact he.symm

/-- Replacing one edge color moment in a bounded finite-vertex product costs
at most the cut-norm difference of the two scalar graphons. -/
theorem abs_integral_changed_edge_le {n : ℕ} (a b : Fin n) (hab : a ≠ b)
    (U V : Graphon Ω μ) (r f g : (Fin n → Ω) → ℝ)
    (hr : Measurable r) (hf : Measurable f) (hg : Measurable g)
    (hrb : ∀ z, r z ∈ Set.Icc 0 1) (hfb : ∀ z, f z ∈ Set.Icc 0 1)
    (hgb : ∀ z, g z ∈ Set.Icc 0 1)
    (hra : ∀ z x, r (Function.update z a x) = r z)
    (hrb' : ∀ z y, r (Function.update z b y) = r z)
    (hfb' : ∀ z y, f (Function.update z b y) = f z)
    (hga : ∀ z x, g (Function.update z a x) = g z) :
    |∫ z : Fin n → Ω, r z * f z * g z *
      (U.toAEEqFun (z a, z b) - V.toAEEqFun (z a, z b))
      ∂Measure.pi (fun _ : Fin n => μ)| ≤ Graphon.cutNormDiff U V := by
  let e := splitCoordinates (Ω := Ω) a b hab
  let κ := fun p : Ω × Ω => U.toAEEqFun p - V.toAEEqFun p
  let H := fun z : Fin n → Ω => r z * f z * g z * κ (z a, z b)
  have hκ : Integrable κ (μ.prod μ) :=
    (SymmKernel.graphon_integrable U).sub (SymmKernel.graphon_integrable V)
  have hκpull : Integrable (fun z : Fin n → Ω => κ (z a, z b))
      (Measure.pi (fun _ : Fin n => μ)) :=
    (measurePreserving_pairProjection (μ := μ) a b hab).integrable_comp_of_integrable hκ
  have hweight (z : Fin n → Ω) : r z * f z * g z ∈ Set.Icc 0 1 := by
    have hrf0 : 0 ≤ r z * f z := mul_nonneg (hrb z).1 (hfb z).1
    have hrf1 : r z * f z ≤ 1 := by
      calc
        r z * f z ≤ 1 * f z := mul_le_mul_of_nonneg_right (hrb z).2 (hfb z).1
        _ ≤ 1 := by simpa using (hfb z).2
    exact ⟨mul_nonneg hrf0 (hgb z).1, by
      calc
        r z * f z * g z ≤ 1 * g z := mul_le_mul_of_nonneg_right hrf1 (hgb z).1
        _ ≤ 1 := by simpa using (hgb z).2⟩
  have hH : Integrable H (Measure.pi (fun _ : Fin n => μ)) := by
    apply hκpull.bdd_mul ((hr.mul hf).mul hg).aestronglyMeasurable
    filter_upwards with z
    simpa only [Pi.mul_apply, Real.norm_eq_abs,
      abs_of_nonneg (hweight z).1] using (hweight z).2
  rw [show (∫ z, H z ∂Measure.pi (fun _ : Fin n => μ)) = _ from
    integral_two_coordinates a b hab H hH]
  let tμ : Measure ({i : Fin n // ¬(i = a ∨ i = b)} → Ω) := Measure.pi (fun _ => μ)
  have htint : Integrable (fun t : {i : Fin n // ¬(i = a ∨ i = b)} → Ω =>
      ∫ p : Ω × Ω, H (e.symm (p, t)) ∂μ.prod μ) tμ := by
    have hint : Integrable (fun q : (Ω × Ω) ×
        ({i : Fin n // ¬(i = a ∨ i = b)} → Ω) => H (e.symm q))
        ((μ.prod μ).prod tμ) :=
      ((splitCoordinates_measurePreserving (μ := μ) a b hab).symm.integrable_comp_emb
        e.symm.measurableEmbedding).2 hH
    exact hint.integral_prod_right
  obtain ⟨x₀, _⟩ := nonempty_of_measure_ne_zero (μ := μ) (s := Set.univ) (by simp)
  have hbound (t : {i : Fin n // ¬(i = a ∨ i = b)} → Ω) :
      |∫ p : Ω × Ω, H (e.symm (p, t)) ∂μ.prod μ| ≤
        Graphon.cutNormDiff U V := by
    let z₀ := e.symm ((x₀, x₀), t)
    let R := r z₀
    let F := fun x : Ω => f (e.symm ((x, x₀), t))
    let G := fun y : Ω => g (e.symm ((x₀, y), t))
    have hF : Measurable F := by fun_prop
    have hG : Measurable G := by fun_prop
    have hFb (x : Ω) : F x ∈ Set.Icc 0 1 := hfb _
    have hGb (y : Ω) : G y ∈ Set.Icc 0 1 := hgb _
    have hfactor (x y : Ω) :
        r (e.symm ((x, y), t)) * f (e.symm ((x, y), t)) *
          g (e.symm ((x, y), t)) = R * F x * G y := by
      have h₁ := hra (e.symm ((x₀, y), t)) x
      rw [← splitCoordinates_symm_update_a a b hab x₀ x y t] at h₁
      have h₂ := hrb' z₀ y
      rw [← splitCoordinates_symm_update_b a b hab x₀ x₀ y t] at h₂
      have h₃ := hfb' (e.symm ((x, x₀), t)) y
      rw [← splitCoordinates_symm_update_b a b hab x x₀ y t] at h₃
      have h₄ := hga (e.symm ((x₀, y), t)) x
      rw [← splitCoordinates_symm_update_a a b hab x₀ x y t] at h₄
      rw [h₁, h₂, h₃, h₄]
    have hfg : Integrable (fun p : Ω × Ω => F p.1 * G p.2 * κ p) (μ.prod μ) := by
      apply hκ.bdd_mul ((hF.comp measurable_fst).mul
        (hG.comp measurable_snd)).aestronglyMeasurable
      filter_upwards with p
      have h0 : 0 ≤ F p.1 * G p.2 := mul_nonneg (hFb p.1).1 (hGb p.2).1
      have h1 : F p.1 * G p.2 ≤ 1 := by
        calc
          F p.1 * G p.2 ≤ 1 * G p.2 :=
            mul_le_mul_of_nonneg_right (hFb p.1).2 (hGb p.2).1
          _ ≤ 1 := by simpa using (hGb p.2).2
      simpa only [Pi.mul_apply, Function.comp_apply, Real.norm_eq_abs,
        abs_of_nonneg h0] using h1
    have hcut : |∫ p : Ω × Ω, F p.1 * G p.2 * κ p ∂μ.prod μ| ≤
        Graphon.cutNormDiff U V := by
      rw [integral_prod _ hfg]
      exact Graphon.abs_weighted_integral_diff_le U V F G hF hG hFb hGb
    have heq : (∫ p : Ω × Ω, H (e.symm (p, t)) ∂μ.prod μ) =
        R * ∫ p : Ω × Ω, F p.1 * G p.2 * κ p ∂μ.prod μ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with p
      change r (e.symm (p, t)) * f (e.symm (p, t)) * g (e.symm (p, t)) *
        κ (((e.symm (p, t)) a), ((e.symm (p, t)) b)) =
          R * (F p.1 * G p.2 * κ p)
      rw [show (e.symm (p, t)) a = p.1 from splitCoordinates_symm_apply_a a b hab p t,
        show (e.symm (p, t)) b = p.2 from splitCoordinates_symm_apply_b a b hab p t]
      rw [hfactor p.1 p.2]
      ring
    rw [heq, abs_mul, abs_of_nonneg (hrb z₀).1]
    exact (mul_le_mul_of_nonneg_left hcut (hrb z₀).1).trans (by
      simpa using mul_le_mul_of_nonneg_right (hrb z₀).2 (Graphon.cutNormDiff_nonneg U V))
  calc
    |∫ t, ∫ p : Ω × Ω, H (e.symm (p, t)) ∂μ.prod μ ∂tμ| ≤
        ∫ t, |∫ p : Ω × Ω, H (e.symm (p, t)) ∂μ.prod μ| ∂tμ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _ : {i : Fin n // ¬(i = a ∨ i = b)} → Ω,
        Graphon.cutNormDiff U V ∂tμ :=
      integral_mono htint.abs (integrable_const _) hbound
    _ = Graphon.cutNormDiff U V := by simp

end Erdos1017.DecoratedCounting
