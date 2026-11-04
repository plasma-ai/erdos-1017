module

public import Erdos1017.Exclusions.Common.CappedDustAtomization

/-!
# Finite iteration of dust atomizations

Iterating one-bin atomizations finitely many times on the same current law keeps
the fibers and untouched pair charges, and together with the final own-profile
comparison pays the sum of the signed original internal charges
(`objective_sub_sum_internal_le_sq`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical Function

namespace Erdos1017.CappedModel.FiniteDustAtomization

open MultipartiteDustAtomization

local instance {α : Type*} : MeasurableSpace (Option α) := ⊤

/-- Reindex the first new cell and the remaining finite cells without
changing any old label or identifying two distinct new cells. -/
private def stepEquiv (ι : Type*) (n : ℕ) : (ι ⊕ Unit) ⊕ Fin n ≃ ι ⊕ Fin (n + 1) where
  toFun
    | .inl (.inl i) => .inl i
    | .inl (.inr _) => .inr 0
    | .inr k => .inr k.succ
  invFun
    | .inl i => .inl (.inl i)
    | .inr k => Fin.cases (.inl (.inr ())) (fun j => .inr j) k
  left_inv := by
    intro x
    rcases x with (i | u) | k
    · rfl
    · cases u
      rfl
    · rfl
  right_inv := by
    intro x
    cases x with
    | inl i => rfl
    | inr k =>
      induction k using Fin.cases with
      | zero => rfl
      | succ k => rfl

private theorem mapped_fiber {α β Ω : Type*} (e : α ≃ β)
    (q : Ω → Option α) (j : β) :
    (fun x => (q x).map e) ⁻¹' {some j} = q ⁻¹' {some (e.symm j)} := by
  ext x
  cases h : q x with
  | none => simp [h]
  | some i => simp [h, Equiv.eq_symm_apply]

private theorem mapped_none {α β Ω : Type*} (e : α ≃ β) (q : Ω → Option α) :
    (fun x => (q x).map e) ⁻¹' {none} = q ⁻¹' {none} := by
  ext x
  cases h : q x <;> simp [h]

private theorem mapped_support {α β Ω : Type*} (e : α ≃ β)
    (q : Ω → Option α) (x y : Ω) :
    ((q x).map e ≠ (q y).map e ∨ (q x).map e = none) ↔
      (q x ≠ q y ∨ q x = none) := by
  cases hx : q x <;> cases hy : q y <;> simp

variable {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
  {ν : Measure Ω} [IsProbabilityMeasure ν]

/-- Finite iteration of actual one-bin atomizations on the same current
law. Literal fibers and untouched pair charges are retained, and all
objective decrements refer to the original current-law model. -/
theorem exists_model (W : Model Ω ν) (hW : FullFeasible W)
    (labels : Ω → Option ι) (hlabels : Measurable labels)
    (hA : ∀ᵐ p ∂ν.prod ν, W.moment CappedColor.adjacency p =
      if labels p.1 ≠ labels p.2 ∨ labels p.1 = none then 1 else 0)
    (n : ℕ) (C : Fin n → Set Ω)
    (hC : ∀ j, MeasurableSet (C j)) (hCpos : ∀ j, 0 < ν (C j))
    (hdisjoint : Pairwise (Disjoint on C))
    (hCdust : ∀ j, C j ⊆ labels ⁻¹' {none}) :
    ∃ (V : Model Ω ν) (q : Ω → Option (ι ⊕ Fin n)),
      FullFeasible V ∧ Measurable q ∧
      (∀ i, q ⁻¹' {some (.inl i)} = labels ⁻¹' {some i}) ∧
      (∀ j, q ⁻¹' {some (.inr j)} = C j) ∧
      q ⁻¹' {none} = labels ⁻¹' {none} \ ⋃ j, C j ∧
      (∀ᵐ p ∂ν.prod ν, V.moment CappedColor.adjacency p =
        if q p.1 ≠ q p.2 ∨ q p.1 = none then 1 else 0) ∧
      (∀ᵐ p ∂ν.prod ν, (∀ j, p.1 ∉ C j) → (∀ j, p.2 ∉ C j) →
        chargeKernel V p.1 p.2 = chargeKernel W p.1 p.2) ∧
      density V = density W - (∑ j, (ν.real (C j)) ^ 2) / 2 ∧
      objective V = objective W -
        (∑ j, ∫ p in (C j) ×ˢ (C j), chargeKernel W p.1 p.2 ∂ν.prod ν) / 2 := by
  induction n generalizing ι W with
  | zero =>
    let q : Ω → Option (ι ⊕ Fin 0) := fun x => (labels x).map Sum.inl
    have hq : Measurable q :=
      (measurable_of_countable (Option.map (Sum.inl : ι → ι ⊕ Fin 0))).comp hlabels
    refine ⟨W, q, hW, hq, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      ext x
      cases hx : labels x <;> simp [q, hx]
    · intro j
      exact Fin.elim0 j
    · ext x
      cases hx : labels x <;> simp [q, hx]
    · filter_upwards [hA] with p hp
      convert hp using 1
      cases hx : labels p.1 <;> cases hy : labels p.2 <;> simp [q, hx, hy]
    · exact Eventually.of_forall (fun _ _ _ => rfl)
    · simp
    · simp
  | succ n ih =>
    obtain ⟨U, hU, hUA, hUY, hUd, hUc⟩ := DustAtomization.exists_model
      W hW labels hlabels hA (C 0) (hC 0) (hCpos 0) (hCdust 0)
    let firstLabels := atomizedLabels labels (C 0)
    have hfirst : Measurable firstLabels :=
      measurable_atomizedLabels labels hlabels (C 0) (hC 0)
    have htailDust : ∀ j : Fin n, C j.succ ⊆ firstLabels ⁻¹' {none} := by
      intro j x hx
      rw [atomized_dust_fiber]
      exact ⟨hCdust j.succ hx, fun hz =>
        Set.disjoint_left.mp (hdisjoint (Fin.succ_ne_zero j)) hx hz⟩
    have htailDisjoint : Pairwise (Disjoint on fun j : Fin n => C j.succ) :=
      fun i j hij => hdisjoint (fun he => hij (Fin.succ_injective _ he))
    obtain ⟨V, q₀, hV, hq₀, hOld, hNew, hDust, hVA, hVY, hVd, hVc⟩ :=
      ih U hU firstLabels hfirst
        (by
          filter_upwards [] with p
          have hp := hUA p
          split_ifs at hp ⊢ <;> exact hp)
        (fun j => C j.succ) (fun j => hC j.succ) (fun j => hCpos j.succ)
        htailDisjoint htailDust
    let e := stepEquiv ι n
    let q : Ω → Option (ι ⊕ Fin (n + 1)) := fun x => (q₀ x).map e
    have hq : Measurable q := (measurable_of_countable (Option.map e)).comp hq₀
    have hzeroOutside : ∀ᵐ p ∂ν.prod ν,
        p.1 ∉ C 0 → p.2 ∉ C 0 → chargeKernel U p.1 p.2 = chargeKernel W p.1 p.2 := by
      filter_upwards [hUY] with p hp hx hy
      exact hp.trans (atomizedCharge_outside (C 0) _ hx hy)
    have hIntegral (j : Fin n) :
        (∫ p in (C j.succ) ×ˢ (C j.succ), chargeKernel U p.1 p.2 ∂ν.prod ν) =
          ∫ p in (C j.succ) ×ˢ (C j.succ), chargeKernel W p.1 p.2 ∂ν.prod ν := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hzeroOutside,
        ae_restrict_mem ((hC j.succ).prod (hC j.succ))] with p hp hpC
      have hdis := hdisjoint (Fin.succ_ne_zero j)
      exact hp (fun hx => Set.disjoint_left.mp hdis hpC.1 hx)
        (fun hy => Set.disjoint_left.mp hdis hpC.2 hy)
    refine ⟨V, q, hV, hq, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      rw [show q = fun x => (q₀ x).map e from rfl, mapped_fiber]
      change q₀ ⁻¹' {some (.inl (.inl i))} = _
      rw [hOld, atomized_old_fiber labels (C 0) (hCdust 0)]
    · intro j
      induction j using Fin.cases with
      | zero =>
        rw [show q = fun x => (q₀ x).map e from rfl, mapped_fiber]
        change q₀ ⁻¹' {some (.inl (.inr ()))} = _
        rw [hOld, atomized_new_fiber]
      | succ j =>
        rw [show q = fun x => (q₀ x).map e from rfl, mapped_fiber]
        exact hNew j
    · rw [show q = fun x => (q₀ x).map e from rfl, mapped_none, hDust,
        atomized_dust_fiber]
      ext x
      simp only [Set.mem_sdiff, mem_iUnion, not_exists]
      constructor
      · rintro ⟨⟨hx, hzero⟩, htail⟩
        exact ⟨hx, fun j => Fin.cases hzero htail j⟩
      · rintro ⟨hx, hall⟩
        exact ⟨⟨hx, hall 0⟩, fun j => hall j.succ⟩
    · filter_upwards [hVA] with p hp
      have he := mapped_support e q₀ p.1 p.2
      change (_ ≠ _ ∨ _ = none) ↔ (q₀ p.1 ≠ q₀ p.2 ∨ q₀ p.1 = none) at he
      by_cases h : q₀ p.1 ≠ q₀ p.2 ∨ q₀ p.1 = none
      · have hnew : q p.1 ≠ q p.2 ∨ q p.1 = none := he.mpr h
        simpa only [h, hnew, ↓reduceIte] using hp
      · have hnew : ¬(q p.1 ≠ q p.2 ∨ q p.1 = none) := fun hn => h (he.mp hn)
        simpa only [h, hnew, ↓reduceIte] using hp
    · filter_upwards [hVY, hzeroOutside] with p hv hu hx hy
      exact (hv (fun j => hx j.succ) (fun j => hy j.succ)).trans (hu (hx 0) (hy 0))
    · rw [hVd, hUd, Fin.sum_univ_succ]
      ring
    · simp_rw [hIntegral] at hVc
      rw [hVc, hUc, Fin.sum_univ_succ]
      ring

variable [StandardBorelSpace Ω] [NullSingletonClass ν]

/-- Actual finite atomization and the genuine final own-profile comparison
pay the sum of signed original internal charges. -/
theorem objective_sub_sum_internal_le_sq (W : Model Ω ν) (hW : FullFeasible W)
    (labels : Ω → Option ι) (hlabels : Measurable labels)
    (hA : ∀ᵐ p ∂ν.prod ν, W.moment CappedColor.adjacency p =
      if labels p.1 ≠ labels p.2 ∨ labels p.1 = none then 1 else 0)
    (n : ℕ) (C : Fin n → Set Ω)
    (hC : ∀ j, MeasurableSet (C j)) (hCpos : ∀ j, 0 < ν (C j))
    (hdisjoint : Pairwise (Disjoint on C))
    (hCdust : ∀ j, C j ⊆ labels ⁻¹' {none}) (A : ℝ)
    (hclasses : ∀ i, MultipartiteClassMasses.classMass ν labels i ≤ A)
    (hCA : ∀ j, ν.real (C j) ≤ A) :
    objective W -
      (∑ j, ∫ p in (C j) ×ˢ (C j), chargeKernel W p.1 p.2 ∂ν.prod ν) / 2 ≤ A ^ 2 := by
  obtain ⟨V, q, hV, hq, hOld, hNew, _, hVA, _, _, hVc⟩ :=
    exists_model W hW labels hlabels hA n C hC hCpos hdisjoint hCdust
  have hparts : ∀ k, MultipartiteClassMasses.classMass ν q k ≤ A := by
    intro k
    cases k with
    | inl i => simpa only [MultipartiteClassMasses.classMass, hOld] using hclasses i
    | inr j => simpa only [MultipartiteClassMasses.classMass, hNew] using hCA j
  have h := MultipartiteClassMasses.objective_le_class_bound_sq V hV q hq
    (by
      filter_upwards [hVA] with p hp
      split_ifs at hp ⊢ <;> exact hp) A hparts
  rwa [hVc] at h

end Erdos1017.CappedModel.FiniteDustAtomization
