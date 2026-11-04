module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Multipartite support on the two half graphs

Atomic points keep their whole-fiber label and remainder points get singleton
dust labels (`atomicDustLabel`), or dust collapses to one marker
(`collapsedLabel`); with strict support and zero coverage, both original half
graphs then have complete-multipartite adjacency support away from the null
diagonal.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Classical

namespace Erdos1017.HalfGraphMultipartite

variable {Ω L : Type*} [MeasurableSpace Ω] [MeasurableSpace L]
  [MeasurableSingletonClass L] {μ : Measure Ω}

/-- Two points lie in the same original independent whole fiber. -/
def sameAtom (R : Ω → L) (I : Set L) (x y : Ω) : Prop :=
  ∃ r ∈ I, R x = r ∧ R y = r

/-- Atomic points retain their original whole-fiber value; each remainder
point has its own genuine singleton dust label. -/
def atomicDustLabel (R : Ω → L) (I : Set L) (x : Ω) : I ⊕ Ω :=
  if h : R x ∈ I then Sum.inl ⟨R x, h⟩ else Sum.inr x

/-- The value-comparison adapter may collapse dust to none, provided none
is treated as clique dust by the support disjunction below. -/
def collapsedLabel (R : Ω → L) (I : Set L) (x : Ω) : Option I :=
  if h : R x ∈ I then some ⟨R x, h⟩ else none

omit [MeasurableSpace Ω] [MeasurableSpace L] [MeasurableSingletonClass L] in
/-- The atomic label's level set is exactly the original whole fiber. -/
theorem atomicDustLabel_eq_inl_iff (R : Ω → L) (I : Set L) (x : Ω) (r : I) :
    atomicDustLabel R I x = Sum.inl r ↔ R x = (r : L) := by
  classical
  by_cases hx : R x ∈ I
  · simp only [atomicDustLabel, hx, ↓reduceDIte, Sum.inl.injEq, Subtype.ext_iff]
  · simp only [atomicDustLabel, hx, ↓reduceDIte, reduceCtorEq, false_iff]
    exact fun he => hx (he.symm ▸ r.property)

omit [MeasurableSpace Ω] [MeasurableSpace L] [MeasurableSingletonClass L] in
/-- Each genuine dust label has a singleton level set in the remainder. -/
theorem atomicDustLabel_eq_inr_iff (R : Ω → L) (I : Set L) (x y : Ω) :
    atomicDustLabel R I x = Sum.inr y ↔ R x ∉ I ∧ x = y := by
  classical
  by_cases hx : R x ∈ I <;> simp [atomicDustLabel, hx]

omit [MeasurableSpace Ω] [MeasurableSpace L] [MeasurableSingletonClass L] in
/-- Only the actual remainder receives the collapsed clique-dust marker. -/
theorem collapsedLabel_eq_none_iff (R : Ω → L) (I : Set L) (x : Ω) :
    collapsedLabel R I x = none ↔ R x ∉ I := by
  classical
  by_cases hx : R x ∈ I <;> simp [collapsedLabel, hx]

/-- The dust is the measurable complement of the original whole-fiber union. -/
theorem measurableSet_dust (R : Ω → L) (hR : Measurable R)
    (I : Set L) (hI : I.Countable) : MeasurableSet {x | R x ∉ I} :=
  (hR hI.measurableSet).compl

theorem measurable_atomicDustLabel (R : Ω → L) (hR : Measurable R)
    (I : Set L) (hI : I.Countable) : Measurable (atomicDustLabel R I) := by
  classical
  let s := {x | R x ∈ I}
  have hs : MeasurableSet s := hR hI.measurableSet
  have hr : Measurable (fun x : s => (⟨R x, x.property⟩ : I)) :=
    (hR.comp measurable_subtype_coe).subtype_mk
  have ha : Measurable (fun x : s => (Sum.inl (⟨R x, x.property⟩ : I) : I ⊕ Ω)) :=
    measurable_inl.comp hr
  have hd : Measurable (fun x : (sᶜ : Set Ω) => (Sum.inr (x : Ω) : I ⊕ Ω)) :=
    measurable_inr.comp measurable_subtype_coe
  convert ha.dite hd hs using 1
  funext x
  by_cases hx : R x ∈ I <;> simp only [atomicDustLabel, s, mem_ofPred_eq, hx, ↓reduceDIte]

/-- Countable atomic labels and the extra dust marker carry the discrete
measurable structure used by the conditional multipartite value sampler. -/
theorem measurable_collapsedLabel (R : Ω → L) (hR : Measurable R)
    (I : Set L) (hI : I.Countable) :
    @Measurable Ω (Option I) _ ⊤ (collapsedLabel R I) := by
  classical
  let : MeasurableSpace (Option I) := ⊤
  have : Countable I := hI.to_subtype
  let s := {x | R x ∈ I}
  have hs : MeasurableSet s := hR hI.measurableSet
  have hr : Measurable (fun x : s => (⟨R x, x.property⟩ : I)) :=
    (hR.comp measurable_subtype_coe).subtype_mk
  have ha : Measurable (fun x : s => some (⟨R x, x.property⟩ : I)) :=
    (measurable_of_countable (some : I → Option I)).comp hr
  have hd : Measurable (fun _ : (sᶜ : Set Ω) => (none : Option I)) := measurable_const
  convert ha.dite hd hs using 1
  funext x
  by_cases hx : R x ∈ I <;> simp only [collapsedLabel, s, mem_ofPred_eq, hx, ↓reduceDIte]

omit [MeasurableSpace Ω] [MeasurableSpace L] [MeasurableSingletonClass L] in
/-- The collapsed marker identifies precisely the original atomic fibers;
two dust points with marker none are not declared an independent class. -/
theorem sameAtom_iff_collapsedLabel (R : Ω → L) (I : Set L) (x y : Ω) :
    sameAtom R I x y ↔ collapsedLabel R I x = collapsedLabel R I y ∧
      collapsedLabel R I x ≠ none := by
  classical
  constructor
  · rintro ⟨r, hr, hx, hy⟩
    have hxI : R x ∈ I := hx.symm ▸ hr
    have hyI : R y ∈ I := hy.symm ▸ hr
    have he : (⟨R x, hxI⟩ : I) = ⟨R y, hyI⟩ := Subtype.ext (hx.trans hy.symm)
    simp only [collapsedLabel, hxI, hyI, ↓reduceDIte, he, ne_eq,
      reduceCtorEq, not_false_eq_true, and_self]
  · rintro ⟨heq, hne⟩
    by_cases hxI : R x ∈ I
    · by_cases hyI : R y ∈ I
      · have he : (⟨R x, hxI⟩ : I) = ⟨R y, hyI⟩ := by
          simpa only [collapsedLabel, hxI, hyI, ↓reduceDIte, Option.some.injEq] using heq
        exact ⟨R x, hxI, rfl, (congrArg Subtype.val he).symm⟩
      · simp only [collapsedLabel, hxI, hyI, ↓reduceDIte, reduceCtorEq] at heq
    · exact False.elim (hne (by simp only [collapsedLabel, hxI, ↓reduceDIte]))

omit [MeasurableSpace Ω] [MeasurableSpace L] [MeasurableSingletonClass L] in
/-- The correct collapsed support condition includes every dust-dust pair. -/
theorem collapsed_clique_condition_iff (R : Ω → L) (I : Set L) (x y : Ω) :
    (collapsedLabel R I x ≠ collapsedLabel R I y ∨ collapsedLabel R I x = none) ↔
      ¬sameAtom R I x y := by
  classical
  rw [sameAtom_iff_collapsedLabel]
  simp only [not_and_or, not_not]

omit [MeasurableSpace Ω] [MeasurableSpace L] [MeasurableSingletonClass L] in
/-- Away from the physical diagonal, equality of genuine labels is exactly
membership in a common original independent whole fiber. -/
theorem atomicDustLabel_eq_iff_of_ne (R : Ω → L) (I : Set L) {x y : Ω} (hxy : x ≠ y) :
    atomicDustLabel R I x = atomicDustLabel R I y ↔ sameAtom R I x y := by
  classical
  constructor
  · intro heq
    by_cases hxI : R x ∈ I
    · by_cases hyI : R y ∈ I
      · have he : (⟨R x, hxI⟩ : I) = ⟨R y, hyI⟩ := by
          simpa only [atomicDustLabel, hxI, hyI, ↓reduceDIte, Sum.inl.injEq] using heq
        exact ⟨R x, hxI, rfl, (congrArg Subtype.val he).symm⟩
      · simp only [atomicDustLabel, hxI, hyI, ↓reduceDIte, reduceCtorEq] at heq
    · by_cases hyI : R y ∈ I
      · simp only [atomicDustLabel, hxI, hyI, ↓reduceDIte, reduceCtorEq] at heq
      · exact False.elim (hxy (by
          simpa only [atomicDustLabel, hxI, hyI, ↓reduceDIte, Sum.inr.injEq] using heq))
  · rintro ⟨r, hr, hx, hy⟩
    have hxI : R x ∈ I := hx.symm ▸ hr
    have hyI : R y ∈ I := hy.symm ▸ hr
    have he : (⟨R x, hxI⟩ : I) = ⟨R y, hyI⟩ := Subtype.ext (hx.trans hy.symm)
    simp only [atomicDustLabel, hxI, hyI, ↓reduceDIte, he]

variable [IsFiniteMeasure μ]

/-- The countably many actual independent fiber-square events have one
global AE implication for common atomic labels. -/
theorem ae_sameAtom_adjacency_zero
    (G : Ω → Ω → ℝ) (R : Ω → L) (hR : Measurable R) (I : Set L) (hI : I.Countable)
    (hindependent : ∀ r ∈ I, ∀ᵐ p ∂(μ.restrict {x | R x = r}).prod
      (μ.restrict {x | R x = r}), G p.1 p.2 = 0) :
    ∀ᵐ p ∂μ.prod μ, sameAtom R I p.1 p.2 → G p.1 p.2 = 0 := by
  have hcommon : ∀ᵐ p ∂μ.prod μ, ∀ r ∈ I,
      R p.1 = r → R p.2 = r → G p.1 p.2 = 0 := by
    apply (ae_ball_iff hI).mpr
    intro r hr
    have hmeas := hR (measurableSet_singleton r)
    have hi := hindependent r hr
    rw [Measure.prod_restrict] at hi
    filter_upwards [(ae_restrict_iff' (hmeas.prod hmeas)).mp hi] with p hp hx hy
    exact hp ⟨hx, hy⟩
  filter_upwards [hcommon] with p hp hsame
  obtain ⟨r, hr, hx, hy⟩ := hsame
  exact hp r hr hx hy

/-- Original strict support and actual zero coverage derive the completed
clique-dust support on any set with no internal outside-zero pairs. -/
theorem ae_collapsed_support_on_set
    (K G : Ω → Ω → ℝ) (R : Ω → L) (hR : Measurable R) (I : Set L) (hI : I.Countable)
    (hindependent : ∀ r ∈ I, ∀ᵐ p ∂(μ.restrict {x | R x = r}).prod
      (μ.restrict {x | R x = r}), G p.1 p.2 = 0)
    (hK0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ K p.1 p.2)
    (hsupport : ∀ᵐ p ∂μ.prod μ, G p.1 p.2 = if 0 < K p.1 p.2 then 1 else 0)
    (Z : Set (Ω × Ω))
    (hzeroCover : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = 0 → sameAtom R I p.1 p.2 ∨ p ∈ Z)
    (T : Set Ω) (hnoZ : ∀ᵐ p ∂(μ.restrict T).prod (μ.restrict T), p ∉ Z) :
    ∀ᵐ p ∂(μ.restrict T).prod (μ.restrict T), G p.1 p.2 =
      if collapsedLabel R I p.1 ≠ collapsedLabel R I p.2 ∨ collapsedLabel R I p.1 = none
      then 1 else 0 := by
  have hle : (μ.restrict T).prod (μ.restrict T) ≤ μ.prod μ :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  filter_upwards [ae_mono hle (ae_sameAtom_adjacency_zero G R hR I hI hindependent),
    ae_mono hle hK0, ae_mono hle hsupport, ae_mono hle hzeroCover, hnoZ]
    with p hi hk hs hz hn
  by_cases ha : sameAtom R I p.1 p.2
  · have hcond : ¬(collapsedLabel R I p.1 ≠ collapsedLabel R I p.2 ∨
        collapsedLabel R I p.1 = none) := fun h => (collapsed_clique_condition_iff R I _ _).mp h ha
    rw [ite_eq_right hcond]
    exact hi ha
  · have hne : K p.1 p.2 ≠ 0 := fun h => (hz h).elim ha hn
    have hpos : 0 < K p.1 p.2 := lt_of_le_of_ne hk hne.symm
    have hcond := (collapsed_clique_condition_iff R I p.1 p.2).mpr ha
    rw [ite_eq_left hcond, hs, ite_eq_left hpos]

/-- Null singletons and measurable equality give the genuine physical
pair-diagonal nullity required by singleton dust labels. -/
theorem ae_coordinates_ne [MeasurableEq Ω] [NullSingletonClass μ] :
    ∀ᵐ p : Ω × Ω ∂μ.prod μ, p.1 ≠ p.2 := by
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_eq_fun measurable_fst measurable_snd).compl).mpr
  exact Filter.Eventually.of_forall (fun x => (μ.ae_ne x).mono (fun _ hy => hy.symm))

omit [MeasurableSpace L] [MeasurableSingletonClass L] in
/-- Genuine singleton-dust labels have ordinary complete-multipartite
inequality support away from the derived null physical diagonal. -/
theorem ae_atomicDust_support_on_set [MeasurableEq Ω] [NullSingletonClass μ]
    (G : Ω → Ω → ℝ) (R : Ω → L) (I : Set L) (T : Set Ω)
    (hcollapsed : ∀ᵐ p ∂(μ.restrict T).prod (μ.restrict T), G p.1 p.2 =
      if collapsedLabel R I p.1 ≠ collapsedLabel R I p.2 ∨ collapsedLabel R I p.1 = none
      then 1 else 0) :
    ∀ᵐ p ∂(μ.restrict T).prod (μ.restrict T), G p.1 p.2 =
      if atomicDustLabel R I p.1 ≠ atomicDustLabel R I p.2 then 1 else 0 := by
  have hle : (μ.restrict T).prod (μ.restrict T) ≤ μ.prod μ :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  filter_upwards [hcollapsed, ae_mono hle (ae_coordinates_ne (μ := μ))] with p hp hne
  have hc : (collapsedLabel R I p.1 ≠ collapsedLabel R I p.2 ∨ collapsedLabel R I p.1 = none) ↔
      atomicDustLabel R I p.1 ≠ atomicDustLabel R I p.2 :=
    (collapsed_clique_condition_iff R I _ _).trans
      (not_congr (atomicDustLabel_eq_iff_of_ne R I hne)).symm
  simpa only [hc] using hp

/-- Outside-zero crossing and disjoint class sets remove all internal
outside-zero pairs from each displayed half, including its neutral part. -/
theorem ae_no_outside_pairs_on_halves
    (Z : Set (Ω × Ω)) (H Lo N : Set Ω)
    (hH : MeasurableSet H) (hLo : MeasurableSet Lo) (hN : MeasurableSet N)
    (hHL : Disjoint H Lo) (hHN : Disjoint H N) (hLN : Disjoint Lo N)
    (hcross : ∀ᵐ p ∂μ.prod μ, p ∈ Z →
      (p.1 ∈ H ∧ p.2 ∈ Lo) ∨ (p.2 ∈ H ∧ p.1 ∈ Lo)) :
    (∀ᵐ p ∂(μ.restrict (H ∪ N)).prod (μ.restrict (H ∪ N)), p ∉ Z) ∧
      (∀ᵐ p ∂(μ.restrict (Lo ∪ N)).prod (μ.restrict (Lo ∪ N)), p ∉ Z) := by
  have hnotLo (x : Ω) (hx : x ∈ H ∪ N) : x ∉ Lo := by
    intro hy
    rcases hx with hx | hx
    · exact Set.disjoint_left.mp hHL hx hy
    · exact Set.disjoint_left.mp hLN hy hx
  have hnotH (x : Ω) (hx : x ∈ Lo ∪ N) : x ∉ H := by
    intro hy
    rcases hx with hx | hx
    · exact Set.disjoint_left.mp hHL hy hx
    · exact Set.disjoint_left.mp hHN hy hx
  constructor
  · have hle : (μ.restrict (H ∪ N)).prod (μ.restrict (H ∪ N)) ≤ μ.prod μ :=
      Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
    filter_upwards [ae_mono hle hcross,
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem (hH.union hN)),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem (hH.union hN))] with p hp hx hy hz
    exact (hp hz).elim (fun h => hnotLo _ hy h.2) (fun h => hnotLo _ hx h.2)
  · have hle : (μ.restrict (Lo ∪ N)).prod (μ.restrict (Lo ∪ N)) ≤ μ.prod μ :=
      Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
    filter_upwards [ae_mono hle hcross,
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem (hLo.union hN)),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem (hLo.union hN))] with p hp hx hy hz
    exact (hp hz).elim (fun h => hnotH _ hx h.1) (fun h => hnotH _ hy h.1)

/-- Both original half graphs have the actual collapsed clique-dust support.
Zero coverage remains the explicit generic original-kernel premise, not an
assumed multipartite partition support. -/
theorem ae_collapsed_support_on_halves
    (K G : Ω → Ω → ℝ) (R : Ω → L) (hR : Measurable R) (I : Set L) (hI : I.Countable)
    (hindependent : ∀ r ∈ I, ∀ᵐ p ∂(μ.restrict {x | R x = r}).prod
      (μ.restrict {x | R x = r}), G p.1 p.2 = 0)
    (hK0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ K p.1 p.2)
    (hsupport : ∀ᵐ p ∂μ.prod μ, G p.1 p.2 = if 0 < K p.1 p.2 then 1 else 0)
    (Z : Set (Ω × Ω))
    (hzeroCover : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = 0 → sameAtom R I p.1 p.2 ∨ p ∈ Z)
    (H Lo N : Set Ω) (hH : MeasurableSet H) (hLo : MeasurableSet Lo) (hN : MeasurableSet N)
    (hHL : Disjoint H Lo) (hHN : Disjoint H N) (hLN : Disjoint Lo N)
    (hcross : ∀ᵐ p ∂μ.prod μ, p ∈ Z →
      (p.1 ∈ H ∧ p.2 ∈ Lo) ∨ (p.2 ∈ H ∧ p.1 ∈ Lo)) :
    (∀ᵐ p ∂(μ.restrict (H ∪ N)).prod (μ.restrict (H ∪ N)), G p.1 p.2 =
      if collapsedLabel R I p.1 ≠ collapsedLabel R I p.2 ∨ collapsedLabel R I p.1 = none
      then 1 else 0) ∧
    (∀ᵐ p ∂(μ.restrict (Lo ∪ N)).prod (μ.restrict (Lo ∪ N)), G p.1 p.2 =
      if collapsedLabel R I p.1 ≠ collapsedLabel R I p.2 ∨ collapsedLabel R I p.1 = none
      then 1 else 0) := by
  obtain ⟨hh, hl⟩ := ae_no_outside_pairs_on_halves Z H Lo N hH hLo hN hHL hHN hLN hcross
  exact ⟨ae_collapsed_support_on_set K G R hR I hI hindependent hK0 hsupport Z hzeroCover _ hh,
    ae_collapsed_support_on_set K G R hR I hI hindependent hK0 hsupport Z hzeroCover _ hl⟩

/-- The same original independent classes and genuine singleton dust give
ordinary complete-multipartite adjacency support on both original halves.
Only this dust-diagonal step needs null singletons and measurable equality. -/
theorem ae_atomicDust_support_on_halves [MeasurableEq Ω] [NullSingletonClass μ]
    (K G : Ω → Ω → ℝ) (R : Ω → L) (hR : Measurable R) (I : Set L) (hI : I.Countable)
    (hindependent : ∀ r ∈ I, ∀ᵐ p ∂(μ.restrict {x | R x = r}).prod
      (μ.restrict {x | R x = r}), G p.1 p.2 = 0)
    (hK0 : ∀ᵐ p ∂μ.prod μ, 0 ≤ K p.1 p.2)
    (hsupport : ∀ᵐ p ∂μ.prod μ, G p.1 p.2 = if 0 < K p.1 p.2 then 1 else 0)
    (Z : Set (Ω × Ω))
    (hzeroCover : ∀ᵐ p ∂μ.prod μ, K p.1 p.2 = 0 → sameAtom R I p.1 p.2 ∨ p ∈ Z)
    (H Lo N : Set Ω) (hH : MeasurableSet H) (hLo : MeasurableSet Lo) (hN : MeasurableSet N)
    (hHL : Disjoint H Lo) (hHN : Disjoint H N) (hLN : Disjoint Lo N)
    (hcross : ∀ᵐ p ∂μ.prod μ, p ∈ Z →
      (p.1 ∈ H ∧ p.2 ∈ Lo) ∨ (p.2 ∈ H ∧ p.1 ∈ Lo)) :
    (∀ᵐ p ∂(μ.restrict (H ∪ N)).prod (μ.restrict (H ∪ N)), G p.1 p.2 =
      if atomicDustLabel R I p.1 ≠ atomicDustLabel R I p.2 then 1 else 0) ∧
    (∀ᵐ p ∂(μ.restrict (Lo ∪ N)).prod (μ.restrict (Lo ∪ N)), G p.1 p.2 =
      if atomicDustLabel R I p.1 ≠ atomicDustLabel R I p.2 then 1 else 0) := by
  obtain ⟨hh, hl⟩ := ae_collapsed_support_on_halves K G R hR I hI hindependent hK0 hsupport
    Z hzeroCover H Lo N hH hLo hN hHL hHN hLN hcross
  exact ⟨ae_atomicDust_support_on_set G R I _ hh, ae_atomicDust_support_on_set G R I _ hl⟩

end Erdos1017.HalfGraphMultipartite
